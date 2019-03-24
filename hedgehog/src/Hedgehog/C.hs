{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Hedgehog.C where

import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.Trans.Except (ExceptT(..), runExceptT, except)
import           Data.Data (Data(..))
import           Data.Either (either)
import           Data.Foldable (traverse_)
import qualified Data.Generics.Uniplate.Data as Uniplate
import           Data.IORef (IORef)
import qualified Data.IORef as IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import           Foreign.C.Types
import           Foreign.Ptr (Ptr)
import           Foreign.Storable (Storable)
import           Foreign.Store (Store)
import qualified Foreign.Store as Store
import           Hedgehog.Internal.Show (showPretty)
import qualified Language.C as C
import qualified Language.C.Analysis as C
import qualified Language.C.Data.Ident as C
import qualified Language.C.Data.Position as C
import qualified Language.C.Parser as C
import qualified Language.C.Pretty as C
import qualified Language.C.Syntax as C
import qualified Language.C.System.GCC as C
import           Language.Haskell.TH (Q, TExp)
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import           Language.Haskell.TH.Lift (deriveLift)
import           System.Directory (getDirectoryContents)
import           System.FilePath ((</>), takeDirectory, takeExtension, makeRelative)
import           System.IO.Unsafe (unsafePerformIO)
import           System.Posix.DynamicLinker (DL, RTLDFlags(..), dlopen, dlclose)
import           Text.PrettyPrint.Annotated.WL (Doc, (<+>))
import qualified Text.PrettyPrint.Annotated.WL as WL

data Config =
  Config {
    configGcc :: FilePath
  , configExtraIncludes :: [FilePath]
  , configCHeaders :: [FilePath]
  , configCLibrary :: FilePath
  } deriving (Eq, Ord, Show)

defaultConfig :: Config
defaultConfig =
  Config {
      configGcc =
        "gcc"
    , configExtraIncludes =
        []
    , configCHeaders =
        []
    , configCLibrary =
        "lib.o"
    }

unIdent :: C.Ident -> String
unIdent x0 =
  case x0 of
    C.Ident x _ _ ->
      x

position :: C.Position
position =
  C.position 0 "" 0 0 Nothing

posLength :: (C.Position, Int)
posLength =
  (position, 0)

removeNodeInfo :: C.NodeInfo -> C.NodeInfo
removeNodeInfo info =
  case info of
    C.NodeInfo _ _ _ ->
      C.OnlyPos position posLength
    _ ->
      info

data Header =
  Header {
      headerPath :: FilePath
    , headerTypedefs :: [String]
    , headerFunctions :: [Function]
    } deriving (Eq, Ord, Show)

data Function =
  Function {
      functionName :: String
    , functionResult :: Type
    , functionParameters :: [Parameter]
    } deriving (Eq, Ord, Show)

data Type =
    Void
  | Bool
  | Char
  | SChar
  | UChar
  | Short
  | UShort
  | Int
  | UInt
  | Long
  | ULong
  | LLong
  | ULLong
  | Float
  | Double
  | TypedefPtr String
  | Ptr Type
    deriving (Eq, Ord, Show)

data Parameter =
  Parameter (Maybe String) Type
  deriving (Eq, Ord, Show)

--ppCommands :: [String] -> [Function] -> Doc ()
--ppCommands typedefs functions =
--  WL.vsep (fmap ppTypedef typedefs) WL.<#>
--  WL.vsep (fmap ppFunction functions)
--
--ppTypedef :: String -> Doc ()
--ppTypedef name =
--  "data " <> WL.text name <> " = " <> WL.text name
--
--ppFunction :: Function -> Doc ()
--ppFunction (Function name result xs) =
--  "foreign import ccall \"" <>
--  WL.text name <>
--  "\" " <> WL.text name <>
--  " :: " <> WL.hsep (WL.punctuate " ->"
--    (fmap (ppType . parameterType) xs <>
--    ["IO " <> ppTypeParen result]))
--
--ppTypeParen :: Type -> Doc ()
--ppTypeParen x0 =
--  case x0 of
--  Ptr _ ->
--    "(" <> ppType x0 <> ")"
--  _ ->
--   ppType x0
--
--ppType :: Type -> Doc ()
--ppType x0 =
--  case x0 of
--    Void ->
--      "()"
--    Bool ->
--      "CBool"
--    Char ->
--      "CChar"
--    SChar ->
--      "CSChar"
--    UChar ->
--      "CUChar"
--    Short ->
--      "CShort"
--    UShort ->
--      "CUShort"
--    Int ->
--      "CInt"
--    UInt ->
--      "CUInt"
--    Long ->
--      "CLong"
--    ULong ->
--      "CULong"
--    LLong ->
--      "CLLong"
--    ULLong ->
--      "CULLong"
--    Float ->
--      "CFloat"
--    Double ->
--      "CDouble"
--    TypedefPtr xs ->
--      WL.text xs
--    Ptr x ->
--      "Ptr " <> ppTypeParen x

takeFunType :: C.IdentDecl -> Maybe Function
takeFunType decl =
  case decl of
    C.Declaration (C.Decl (C.VarDecl
      (C.VarName name _) _ (C.FunctionType (C.FunType ret args _) _)) _) ->
        Function
          <$> pure (unIdent name)
          <*> takeType ret
          <*> traverse takeParameter args
    _ ->
        Nothing

parameterType :: Parameter -> Type
parameterType (Parameter _ x) =
  x

takeParameter :: C.ParamDecl -> Maybe Parameter
takeParameter decl =
  case decl of
    C.ParamDecl (C.VarDecl (C.VarName name _) _ typ) _ ->
     Parameter
       <$> pure (Just (unIdent name))
       <*> takeType typ

    C.ParamDecl (C.VarDecl C.NoName _ typ) _ ->
     Parameter
       <$> Nothing
       <*> takeType typ

    _ ->
      error (show decl)

takeTypeDefRef :: C.TypeDefRef -> String
takeTypeDefRef = \case
  C.TypeDefRef ident _ _ ->
    unIdent ident

takeType :: C.Type -> Maybe Type
takeType x0 =
  case x0 of
    C.DirectType C.TyVoid _ _ ->
      Just Void
    C.DirectType (C.TyIntegral C.TyBool) _ _ ->
      Just Bool
    C.DirectType (C.TyIntegral C.TyChar) _ _ ->
      Just Char
    C.DirectType (C.TyIntegral C.TySChar) _ _ ->
      Just SChar
    C.DirectType (C.TyIntegral C.TyUChar) _ _ ->
      Just UChar
    C.DirectType (C.TyIntegral C.TyShort) _ _ ->
      Just Short
    C.DirectType (C.TyIntegral C.TyUShort) _ _ ->
      Just UShort
    C.DirectType (C.TyIntegral C.TyInt) _ _ ->
      Just Int
    C.DirectType (C.TyIntegral C.TyUInt) _ _ ->
      Just UInt
    C.DirectType (C.TyIntegral C.TyLong) _ _ ->
      Just Long
    C.DirectType (C.TyIntegral C.TyULong) _ _ ->
      Just ULong
    C.DirectType (C.TyIntegral C.TyLLong) _ _ ->
      Just LLong
    C.DirectType (C.TyIntegral C.TyULLong) _ _ ->
      Just ULLong
    C.DirectType (C.TyFloating C.TyFloat) _ _ ->
      Just Float
    C.DirectType (C.TyFloating C.TyDouble) _ _ ->
      Just Double
    C.DirectType (C.TyFloating C.TyLDouble) _ _ ->
      Nothing
    C.DirectType (C.TyFloating (C.TyFloatN _ _)) _ _ ->
      Nothing
    C.DirectType (C.TyBuiltin C.TyVaList) _ _ ->
      Nothing
    C.DirectType (C.TyBuiltin C.TyAny) _ _ ->
      Nothing
    C.PtrType (C.TypeDefType (C.TypeDefRef name _ _) _ _) _ _ ->
      Just . TypedefPtr $ unIdent name
    C.PtrType x _ _ ->
      Ptr <$> takeType x
    _ ->
      error (show x0)

parseHeaderSources :: Config -> IO (Either C.ParseError [(FilePath, C.CTranslUnit)])
parseHeaderSources config =
  let
    parse header =
      ExceptT . fmap (fmap (header,)) $
        C.parseCFile
          (C.newGCC $ configGcc config)
          Nothing
          (configExtraIncludes config)
          header
  in
    runExceptT $
      traverse parse (configCHeaders config)

summarizeAST :: FilePath -> C.CTranslUnit -> Either [C.CError] Header
summarizeAST path ast = do
  (decls, _) <- C.runTrav_ (C.analyseAST ast)

  let
    functions =
      Maybe.mapMaybe takeFunType .
      Uniplate.transformBi removeNodeInfo .
      Map.elems .
      Map.filterWithKey (\k _ -> not . List.isPrefixOf "__"  $ unIdent k) .
      C.gObjs $
      decls

    typedefs =
      List.nub .
      fmap takeTypeDefRef .
      Uniplate.universeBi .
      Uniplate.transformBi removeNodeInfo .
      Map.elems .
      Map.filterWithKey (\k _ -> not . List.isPrefixOf "__"  $ unIdent k) .
      C.gObjs $
      decls

  pure (Header path typedefs functions)

--  putStrLn (showPretty functions)
--  putStrLn (show (ppCommands typedefs functions))

findCabalRoot :: FilePath -> Q (Maybe FilePath)
findCabalRoot dir = do
  mcabal <- liftIO $
    List.find ((== ".cabal") . takeExtension) <$> getDirectoryContents dir
  case mcabal of
    Nothing ->
      if takeDirectory dir == dir then
        pure Nothing
      else
        findCabalRoot (takeDirectory dir)
    Just _ ->
      pure (Just dir)

projectRoot :: Q FilePath
projectRoot = do
  file <- TH.loc_filename <$> TH.location
  mroot <- findCabalRoot (takeDirectory file)
  case mroot of
    Nothing ->
      pure (takeDirectory file)
    Just dir ->
      pure dir

applyProjectRoot :: FilePath -> Config -> Config
applyProjectRoot root config =
  config {
      configCHeaders =
        fmap (root </>) (configCHeaders config)
    , configCLibrary =
        root </> configCLibrary config
    }

showErrors :: [C.CError] -> String
showErrors xs =
  unlines (fmap show xs)

liftExcept :: (x -> String) -> ExceptT x Q a -> Q a
liftExcept render ex = do
  result <- runExceptT ex
  case result of
    Left x ->
      fail (render x)
    Right x ->
      pure x

lazyBang :: TH.Bang
lazyBang =
  TH.Bang TH.NoSourceUnpackedness TH.NoSourceStrictness

lazy :: TH.Type -> (TH.Bang, TH.Type)
lazy x =
  (lazyBang, x)

generateTypedefPtr :: String -> Q [TH.Dec]
generateTypedefPtr name = do
  eqT <- [t| Eq |]
  ordT <- [t| Ord |]
  showT <- [t| Show |]
  ptrT <- [t| Ptr () |]

  let
    dataName =
      TH.mkName name

    con =
      TH.NormalC dataName [lazy ptrT]

    dat =
      TH.NewtypeD [] dataName [] Nothing con [TH.DerivClause Nothing [
          eqT, ordT, showT
        ]]

  pure [dat]

typeT :: Type -> Q TH.Type
typeT x0 =
  case x0 of
    Void ->
      [t| () |]
    Bool ->
      [t| CBool |]
    Char ->
      [t| CChar |]
    SChar ->
      [t| CSChar |]
    UChar ->
      [t| CUChar |]
    Short ->
      [t| CShort |]
    UShort ->
      [t| CUShort |]
    Int ->
      [t| CInt |]
    UInt ->
      [t| CUInt |]
    Long ->
      [t| CLong |]
    ULong ->
      [t| CULong |]
    LLong ->
      [t| CLLong |]
    ULLong ->
      [t| CULLong |]
    Float ->
      [t| CFloat |]
    Double ->
      [t| CDouble |]
    TypedefPtr x ->
      pure (TH.ConT (TH.mkName x))
    Ptr x ->
      [t| Ptr $(typeT x) |]

generateForeignImport :: Function -> Q TH.Dec
generateForeignImport function = do
  params <- traverse (typeT . parameterType) (functionParameters function)
  result <- [t| IO |] `TH.appT` typeT (functionResult function)

  let
    typ =
      foldr (\x y -> TH.ArrowT `TH.AppT` x `TH.AppT` y) result params

    cName =
      functionName function

    haskellName =
      TH.mkName (functionName function)

    -- TH.Safe means GHC can do a GC during the call
    -- not sure if this is the best default.
    decl =
      TH.ForeignD (TH.ImportF TH.CCall TH.Safe cName haskellName typ)

  pure decl

generateHeaderBinding :: Header -> Q [TH.Dec]
generateHeaderBinding header = do
  typedefs <- concat <$> traverse generateTypedefPtr (headerTypedefs header)
  functions <- traverse generateForeignImport (headerFunctions header)
  pure (typedefs ++ functions)

guessAvailability :: Type -> WL.Doc ()
guessAvailability = \case
  Void ->
    "G"
  Bool ->
    "G"
  Char ->
    "G"
  SChar ->
    "G"
  UChar ->
    "G"
  Short ->
    "G"
  UShort ->
    "G"
  Int ->
    "G"
  UInt ->
    "G"
  Long ->
    "G"
  ULong ->
    "G"
  LLong ->
    "G"
  ULLong ->
    "G"
  Float ->
    "G"
  Double ->
    "G"
  TypedefPtr _ ->
    "V"
  Ptr _ ->
    "V"

ppCommand :: Function -> WL.Doc ()
ppCommand x =
  let
    availabilities =
      fmap (guessAvailability . parameterType) (functionParameters x)
  in
    "$(command '" <> WL.text (functionName x) <>
      " [" <> WL.hcat (WL.punctuate "," availabilities) <> "])"

ppCommands :: FilePath -> Header -> Doc ()
ppCommands root header =
  WL.vsep $ [
      "-- Commands for " <> WL.text (makeRelative root (headerPath header))
    ] ++ fmap ppCommand (headerFunctions header)

loadCLibraryFrom :: FilePath -> FilePath -> IO ()
loadCLibraryFrom root library = do
  mstore <- Store.lookupStore 1

  case mstore of
    Nothing -> do
      lib <- dlopen library [RTLD_LAZY, RTLD_GLOBAL]
      _ <- Store.newStore lib
      putStrLn $ "Loaded " <> makeRelative root library

    Just store -> do
      old <- Store.readStore store
      dlclose old

      new <- dlopen library [RTLD_LAZY, RTLD_GLOBAL]
      Store.writeStore store new
      putStrLn $ "Reloaded " <> makeRelative root library


generate :: Config -> Q [TH.Dec]
generate config0 = do
  root <- projectRoot

  let
    config =
      applyProjectRoot root config0

  asts <- liftExcept show . ExceptT . liftIO $
    parseHeaderSources config

  headers <- liftExcept showErrors . ExceptT . pure $
    traverse (uncurry summarizeAST) asts

  liftIO . putStrLn . show . WL.vsep $ fmap (ppCommands root) headers

  bindings <- concat <$> traverse generateHeaderBinding headers

  let
    libraryE =
      TH.litE (TH.StringL (configCLibrary config))

    rootE =
      TH.litE (TH.StringL root)

  liftIO $ loadCLibraryFrom root (configCLibrary config)

  loader <- [d|
    loadCLibrary :: IO ()
    loadCLibrary = do
      loadCLibraryFrom $(rootE) $(libraryE)
    |]

  pure $ bindings ++ loader

------------------------------------------------------------------------
-- FIXME Replace with DeriveLift when we drop 7.10 support.

$(deriveLift ''Config)

------------------------------------------------------------------------
-- Uncomment these when debugging language-c

deriving instance Show C.IdentDecl
deriving instance Show C.Decl
deriving instance Show C.VarDecl
deriving instance Show C.VarName
deriving instance Show C.DeclAttrs
deriving instance Show C.FunctionAttrs
deriving instance Show C.Attr
deriving instance Show C.Type
deriving instance Show C.TypeName
deriving instance Show C.ObjDef
deriving instance Show C.CompTypeRef
deriving instance Show C.TypeQuals
deriving instance Show C.EnumTypeRef
deriving instance Show C.ArraySize
deriving instance Show C.BuiltinType
deriving instance Show C.FunType
deriving instance Show C.ParamDecl
deriving instance Show C.TypeDefRef
deriving instance Show C.FunDef
deriving instance Show C.Enumerator
deriving instance Show C.EnumType
