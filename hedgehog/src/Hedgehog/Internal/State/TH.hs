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
module Hedgehog.Internal.State.TH where

import           Control.Monad (when, replicateM)
import           Control.Monad.IO.Class (MonadIO(..))
import qualified Data.Char as Char
import           Hedgehog
import           Hedgehog.Internal.Show (showPretty)
import           Language.Haskell.TH
import           Language.Haskell.TH.Lift (deriveLift)

myFunc :: Q Exp
myFunc = do
  x <- reify 'get
  return $ LitE (StringL (show x))


get :: [Int] -> Int -> IO Int
get xs index =
  return (xs !! index)

foo :: Int -> Int
foo x =
  x + 1

-- command_get :: (MonadGen g, MonadIO m) => Gen Get -> [Callback Get CInt] -> Command g m s
-- $(command 'get)

rename :: (String -> String) -> Name -> Name
rename f =
  mkName . f . nameBase

upcase :: String -> String
upcase xs =
  case xs of
    [] ->
      []
    x : xs ->
      Char.toUpper x : xs

upcaseName :: Name -> Name
upcaseName =
  rename upcase

data Function =
  Function {
      functionArguments :: [Type]
    , functionResult :: Type
    } deriving (Eq, Ord, Show)

reifyVarType :: Name -> Q Type
reifyVarType name = do
  x0 <- reify name
  case x0 of
    VarI _ x _ ->
      return x
    _ ->
      fail $ show name ++ " is not a variable / function"

takeFunction :: Type -> Function
takeFunction x0 =
  case x0 of
    ArrowT `AppT` x `AppT` y ->
      let
        Function xs r =
          takeFunction y
      in
        Function (x : xs) r
    x ->
      Function [] x

lazyBang :: Bang
lazyBang =
  Bang NoSourceUnpackedness NoSourceStrictness

lazy :: Type -> (Bang, Type)
lazy x =
  (lazyBang, x)

nameVar :: String -> Q Type
nameVar name =
  pure (VarT (mkName name))

modelVar :: Q Type -> Q Type
modelVar x = do
  [t| Var $(x) $(nameVar "v") |]

-- ((<*>) ((<$>) Register (pure name)) (htraverse f pid))

applyHTraverse :: Q Exp -> Name -> Availability -> Q Exp
applyHTraverse f name = \case
  G ->
    [e| pure $(varE name) |]
  V ->
    [e| htraverse $(f) $(varE name) |]

constructHTraverseTail :: Q Exp -> [(Name, Availability)] -> Q Exp -> Q Exp
constructHTraverseTail f xs0 exp =
  case xs0 of
    [] ->
      exp
    (name, x) : xs ->
      [e| $(exp) <*> $(applyHTraverse f name x) |]

constructHTraverse :: Q Exp -> [(Name, Availability)] -> Q Exp -> Q Exp
constructHTraverse f xs0 exp =
  case xs0 of
    [] ->
      exp
    (name, x) : xs ->
      constructHTraverseTail f xs [e| $(exp) <$> $(applyHTraverse f name x) |]

instanceHTraversable :: Name -> [Availability] -> Q [Dec]
instanceHTraversable name aargs = do
  names <- replicateM (length aargs) (newName "x")

  [d| instance HTraversable $(varT name) where
        htraverse f x =
          case x of
            $(conP name (fmap varP names)) ->
              $(constructHTraverse [e| f |] (zip names aargs) (conE name))
   |]

data Availability =
    G -- | Generated values, always available.
  | V -- | Variables, results of commands, only available during execution.
    deriving (Eq, Ord, Show)

command :: Name -> [Availability] -> Q [Dec]
command name aargs = do
  vtype <- reifyVarType name

  let
    Function gargs result =
      takeFunction vtype

    gargsLength =
      length gargs

    targsLength =
      length aargs

  when (gargsLength /= targsLength) $
    fail $
      show name ++ " has " ++ show gargsLength ++
      " arguments, but " ++ show targsLength ++ " availabilities" ++
      " were provided."

  vargs <- traverse (modelVar . pure) gargs

  let
    deal t g v =
      case t of
        G ->
          g
        V ->
          v

    args =
      zipWith3 deal aargs gargs vargs

    datName =
      upcaseName name

    con =
      NormalC datName (fmap lazy args)

    dat_v =
      [KindedTV (mkName "v") (ArrowT `AppT` StarT `AppT` StarT)]

    dat =
      DataD [] datName dat_v Nothing [con] []

    htraversable =
      instanceHTraversable datName aargs

  --liftIO . putStrLn $ showPretty vtype
  --liftIO . putStrLn $ showPretty (takeFunction vtype)
  liftIO . putStrLn $ pprint dat
  ht <- htraversable
  liftIO . putStrLn $ pprint ht

  return [dat]

------------------------------------------------------------------------
-- FIXME Replace with DeriveLift when we drop 7.10 support.

$(deriveLift ''Availability)
