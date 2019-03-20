{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
module Hedgehog.C where

import           Data.Data (Data(..))
import qualified Data.Generics.Uniplate.Data as Uniplate
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import           Hedgehog.Internal.Show (showPretty)
import qualified Language.C as C
import qualified Language.C.Analysis as C
import qualified Language.C.Data.Ident as C
import qualified Language.C.Data.Position as C
import qualified Language.C.Parser as C
import qualified Language.C.Pretty as C
import qualified Language.C.Syntax as C
import qualified Language.C.System.GCC as C
import           Text.PrettyPrint.Annotated.WL (Doc, (<+>))
import qualified Text.PrettyPrint.Annotated.WL as WL


data Config =
  Config {
    configGcc :: FilePath
  , configExtraIncludes :: [FilePath]
  , configHeader :: FilePath
  }

testConfig :: Config
testConfig =
  Config "gcc" [] "hedgehog-c/test.h"

parseConfig :: Config -> IO (Either C.ParseError C.CTranslUnit)
parseConfig config =
  C.parseCFile
    (C.newGCC $ configGcc config)
    Nothing
    (configExtraIncludes config)
    (configHeader config)

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
    C.NodeInfo x0 x1 _ ->
      C.OnlyPos position posLength
    _ ->
      info

data Function =
  Function {
      functionName :: String
    , functionResult :: Type
    , functionParameters :: [Parameter]
    } deriving (Eq, Ord, Show)

ppCommands :: [Function] -> Doc ()
ppCommands xs =
  WL.vsep (fmap ppFunction xs)

ppFunction :: Function -> Doc ()
ppFunction (Function name result xs) =
  "foreign import ccall \"" <>
  WL.text name <>
  "\" c_" <> WL.text name <>
  " :: " <> WL.hsep (WL.punctuate " ->"
    (fmap ppType (fmap parameterType xs <> [result])))

ppType :: Type -> Doc ()
ppType x0 =
  case x0 of
    Void ->
      "()"
    Bool ->
      "CBool"
    Char ->
      "CChar"
    SChar ->
      "CSChar"
    UChar ->
      "CUChar"
    Short ->
      "CShort"
    UShort ->
      "CUShort"
    Int ->
      "CInt"
    UInt ->
      "CUInt"
    Int128 ->
      "CInt128"
    UInt128 ->
      "CUInt128"
    Long ->
      "CLong"
    ULong ->
      "CULong"
    LLong ->
      "CLLong"
    ULLong ->
      "CULLong"
    Float ->
      "CFloat"
    Double ->
      "CDouble"
    Typedef xs ->
      "C" <> WL.text xs
    Ptr x ->
      "Ptr " <> ppType x

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
  | Int128
  | UInt128
  | Long
  | ULong
  | LLong
  | ULLong
  | Float
  | Double
  | Typedef String
  | Ptr Type
    deriving (Eq, Ord, Show)

data Parameter =
  Parameter (Maybe String) Type
  deriving (Eq, Ord, Show)

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
    C.DirectType (C.TyIntegral C.TyInt128) _ _ ->
      Nothing
    C.DirectType (C.TyIntegral C.TyUInt128) _ _ ->
      Nothing
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
    C.PtrType x _ _ ->
      Ptr <$> takeType x
    C.TypeDefType (C.TypeDefRef name _ _) _ _ ->
      Just . Typedef $ unIdent name
    _ ->
      error (show x0)

compile :: Config -> IO ()
compile config = do
  Right ast <- parseConfig config
  let
    Right (decls, _) =
      C.runTrav_ (C.analyseAST ast)

    objs =
      Maybe.mapMaybe takeFunType .
      Uniplate.transformBi removeNodeInfo .
      Map.elems .
      Map.filterWithKey (\k v -> not . List.isPrefixOf "__"  $ unIdent k) .
      C.gObjs $
      decls

  putStrLn (showPretty objs)
  putStrLn (show (ppCommands objs))

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

tests :: IO ()
tests =
  compile testConfig
