{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Hedgehog.Internal.State.TH (
    Availability(..)
  , command
  ) where

import           Control.Monad (when, replicateM)
import           Control.Monad.IO.Class (MonadIO(..))
import qualified Data.Char as Char
import           Hedgehog
import           Hedgehog.Internal.Show (showPretty)
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (Name(..), NameFlavour(..))
import           Language.Haskell.TH.Syntax (OccName(..), ModName(..))
import           Language.Haskell.TH.Lift (deriveLift)
import qualified Data.Generics.Uniplate.Data as Uniplate

import Debug.Trace

rename :: (String -> String) -> Name -> Name
rename f =
  mkName . f . nameBase

mapHead :: (a -> a) -> [a] -> [a]
mapHead f = \case
  [] ->
    []
  x : xs ->
    f x : xs

data Function =
  Function {
      functionContext :: [Type]
    , functionArguments :: [Argument]
    , functionMonad :: Type
    , functionResult :: Type
    } deriving (Eq, Ord, Show)

data Argument =
  Argument {
      argumentAvailability :: Availability
    , argumentType :: Type
    } deriving (Eq, Ord, Show)

data Availability =
     -- | Generated values, always available.
    Generated
    -- | Variables, results of commands, only available during execution.
  | Variable
    deriving (Eq, Ord, Show)

takeFunctionLoop :: Type -> Type -> Type -> Maybe Function
takeFunctionLoop varType0 v x0 =
  case x0 of
    ForallT _ ctx x -> do
      Function _ xs m r <- takeFunctionLoop varType0 v x
      pure $ Function ctx xs m r

    ArrowT `AppT` arg0@(varType1 `AppT` x `AppT` _v) `AppT` y -> do
      Function ctx xs m r <- takeFunctionLoop varType0 v y
      if (varType0 == varType1) then
        let
          arg1 =
            varType1 `AppT` x `AppT` v
        in
          pure $ Function ctx (Argument Variable arg1 : xs) m r
      else
        pure $ Function ctx (Argument Generated arg0 : xs) m r

    ArrowT `AppT` arg0@(varType1 `AppT` x) `AppT` y -> do
      Function ctx xs m r <- takeFunctionLoop varType0 v y
      if (varType0 == varType1) then
        let
          arg1 =
            varType1 `AppT` x `AppT` v
        in
          pure $ Function ctx (Argument Variable arg1 : xs) m r
      else
        pure $ Function ctx (Argument Generated arg0 : xs) m r

    ArrowT `AppT` x `AppT` y -> do
      Function ctx xs m r <- takeFunctionLoop varType0 v y
      pure $ Function ctx (Argument Generated x : xs) m r

    AppT m x ->
      pure $ Function [] [] m x

    _ ->
      Nothing

takeFunction :: Q Type -> Q (Maybe Function)
takeFunction qtyp = do
  var <- [t| Var |]
  v <- varT (mkName "v")
  typ <- qtyp
  pure (takeFunctionLoop var v typ)

lazyBang :: Bang
lazyBang =
  Bang NoSourceUnpackedness NoSourceStrictness

lazy :: Type -> (Bang, Type)
lazy x =
  (lazyBang, x)

applyHTraverse :: Q Exp -> Name -> Availability -> Q Exp
applyHTraverse f name = \case
  Generated ->
    [e| pure $(varE name) |]
  Variable ->
    [e| htraverse $(f) $(varE name) |]

constructHTraverse :: Q Exp -> [(Name, Availability)] -> Q Exp -> Q Exp
constructHTraverse f xs0 expr =
  case xs0 of
    [] ->
      expr
    (name, x) : xs ->
      constructHTraverse f xs [e| $(expr) <*> $(applyHTraverse f name x) |]

instanceHTraversable :: Name -> [Availability] -> Q [Dec]
instanceHTraversable name aargs = do
  names <- replicateM (length aargs) (newName "x")

  let
    pcon =
      [e| pure $(conE name) |]

  [d| instance HTraversable $(conT name) where
        htraverse _f x =
          case x of
            $(conP name (fmap varP names)) ->
              $(constructHTraverse [e| _f |] (zip names aargs) pcon)
   |]

unwrap :: Availability -> Q Exp -> Q Exp
unwrap availability x =
  case availability of
    Generated ->
      x
    Variable ->
      [| concrete $(x) |]

maybeLiftIO :: Q Type -> Q Exp -> Q Exp
maybeLiftIO qmonad x = do
  monad <- qmonad
  io <- [t| IO |]
  if monad == io then
    [e| liftIO $(x) |]
  else
    x

makeExecuteFunction :: Name -> Q Exp -> Q Type -> [Argument] -> Q Exp
makeExecuteFunction dataName executeE qmonad args = do
  names <- replicateM (length args) (newName "x")

  let
    pats =
      fmap varP names

    exps =
      zipWith ($) (fmap (unwrap . argumentAvailability) args) (fmap varE names)

  lamE [conP dataName pats]
    (maybeLiftIO qmonad $ foldl appE executeE exps)

contextForall :: [Type] -> Q Type -> Q Type
contextForall xs qtyp = do
  typ <- qtyp
  pure $
    ForallT [PlainTV name | VarT name <- Uniplate.universeBi xs] xs typ

liftMonad :: Q Type -> Q (Q Type, [Type])
liftMonad qmonad = do
  io <- [t| IO |]
  monad <- qmonad
  monadIO <- [t| MonadIO |]
  monadVar <- newName "m"
  if monad == io then
    pure (varT monadVar, [monadIO `AppT` VarT monadVar])
  else
    pure (qmonad, [])

commandFromExpression ::
     Name
  -> Q Exp
  -> [Type]
  -> [Argument]
  -> Q Type
  -> Q Type
  -> Q [Dec]
commandFromExpression dataName executeE ctx0 args monad0 resultType = do
  (monad, ctx1) <- liftMonad monad0

  let
    name =
      rename (\x -> mapHead Char.toLower x ++ "From") dataName

  sig <-
    sigD name $ contextForall (ctx0 ++ ctx1) [t|
      forall g s.
      MonadGen g =>
      (s Symbolic -> Maybe (g ($(conT dataName) Symbolic))) ->
      [Callback $(conT dataName) $(resultType) s] ->
      Command g $(monad) s
    |]

  let
    gen =
      mkName "gen"

    callbacks =
      mkName "callbacks"

    body =
      normalB [e|
        let
          execute =
            $(makeExecuteFunction dataName executeE monad0 args)
        in
          Command $(varE gen) execute $(varE callbacks)
      |]

  fun <-
    funD name [clause [varP gen, varP callbacks] body []]

  pure [sig, fun]

command :: String -> Q Type -> Q Exp -> Q [Dec]
command name typ execute = do
  mfunction <- takeFunction typ
  Function ctx args monad result <-
    maybe (fail $ show name ++ " was not monadic.") pure mfunction

  --liftIO . putStrLn $ showPretty mfunction

  eqT <- [t| Eq |]
  ordT <- [t| Ord |]
  showT <- [t| Show |]

  let
    dataName =
      mkName (mapHead Char.toUpper name)

    con =
      NormalC dataName (fmap (lazy . argumentType) args)

    dat_v =
      [KindedTV (mkName "v") (ArrowT `AppT` StarT `AppT` StarT)]

    dat =
      DataD [] dataName dat_v Nothing [con] [DerivClause Nothing [
        eqT, ordT, showT
      ]]

    qhtraversable =
      instanceHTraversable dataName (fmap argumentAvailability args)

    qcommandFrom =
      commandFromExpression dataName execute ctx args (pure monad) (pure result)

  htraversable <- qhtraversable
  commandFrom <- qcommandFrom

  --liftIO $ putStrLn "\n== Extracted Function =="
  --liftIO . putStrLn $ showPretty (takeFunction vtype)
  --liftIO $ putStrLn "\n== Data Type =="
  --liftIO . putStrLn $ pprint dat
  --liftIO $ putStrLn "\n== HTraversable Instance =="
  --liftIO . putStrLn $ pprint ht
  --liftIO $ putStrLn "\n== Command Builder =="
  --liftIO . putStrLn $ pprint mc

  return $ [dat] ++ htraversable ++ commandFrom

------------------------------------------------------------------------
-- FIXME Replace with DeriveLift when we drop 7.10 support.

$(deriveLift ''Availability)
