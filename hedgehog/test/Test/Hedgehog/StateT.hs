{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Example.StateT where

import           Control.Monad (foldM)
import           Control.Monad.Morph (lift)
import           Control.Monad.Reader (ReaderT(..))
import           Control.Monad.State.Class (MonadState(..), modify)
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.Writer.Strict as Strict

import           Data.Functor.Identity (Identity(..))
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Monoid (Last)

import           Hedgehog hiding (Var)
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Gen as Gen

import           Hedgehog.Internal.Distributive (fromStrictStateT, toStrictStateT)


newtype K =
  K Int
  deriving (Eq, Ord, Show, Num)

-- FIXME lol should really just do state machine testing :laughing:
data Statement =
    Get K
  | PutLit Int
  | Put K
  | Inc K
    deriving (Eq, Show)

next :: Monad m => Strict.StateT K m K
next = do
  k <- get
  put (k + 1)
  pure k

random :: MonadGen m => Strict.StateT K m K
random = do
  K k <- get
  if k > 0 then
    K <$> Gen.int (Range.constant 0 (k - 1))
  else
    Gen.discard

evalStatement :: Monad m => Statement -> Strict.StateT (Map K Int) (Strict.StateT Int m) ()
evalStatement = \case
  Get k -> do
    x <- lift get
    modify (Map.insert k x)
  PutLit i ->
    lift $ put i
  Put k -> do
    x <- (\case { Nothing -> undefined; Just x -> x }) . Map.lookup k <$> get
    lift $ put x
  Inc k ->
    modify (Map.insertWith (+) k 1)

evalProgramT :: Monad m => [Statement] -> Strict.StateT Int m ()
evalProgramT ss =
  foldM (const evalStatement) () ss `Strict.evalStateT` Map.empty

evalProgram :: [Statement] -> Strict.State Int ()
evalProgram =
  evalProgramT

genStatement :: Strict.StateT K Gen Statement
genStatement = do
  Gen.choice [
      Get <$> next
    , PutLit <$> Gen.int (Range.constant 0 10)
    , Put <$> random
    , Inc <$> random
    ]

genProgram :: Gen [Statement]
genProgram =
  flip Strict.evalStateT 0 $
    Gen.list (Range.constant 0 50) genStatement

newtype RW =
  RW {
      unRW :: ReaderT Int (Strict.WriterT (Last Int) Identity) ()
    }

instance Show RW where
  show =
    show . Strict.runWriterT . flip runReaderT 0 . unRW

newtype S =
  S {
      unS :: Strict.StateT Int Identity ()
    }

instance Show S where
  show =
    show . flip Strict.runStateT 0 . unS

instance Eq S where
  (==) x y =
    Strict.runStateT (unS x) 0
    ==
    Strict.runStateT (unS y) 0

roundtrip :: Functor m => Strict.StateT s m a -> Strict.StateT s m a
roundtrip =
  toStrictStateT . fromStrictStateT

prop_state :: Property
prop_state =
  withDiscards 1000 $
  property $ do
    x <- forAll genProgram

    cover 90 "size(f) > 0" $ length x > 0
    classify "size(f) = 10" $ length x > 10
    classify "size(f) = 20" $ length x > 20
    classify "size(f) = 30" $ length x > 30
    classify "size(f) = 40" $ length x > 40
    classify "eval(f) > 0" $ Strict.execStateT (evalProgram x) 0 > 0
    classify "eval(f) > 2" $ Strict.execStateT (evalProgram x) 0 > 2
    classify "eval(f) > 4" $ Strict.execStateT (evalProgram x) 0 > 4
    classify "eval(f) > 6" $ Strict.execStateT (evalProgram x) 0 > 6
    classify "eval(f) > 8" $ Strict.execStateT (evalProgram x) 0 > 8
    classify "Get" $ (not . null) [() | Get _ <- x]
    classify "Inc" $ (not . null) [() | Inc _ <- x]
    classify "Put" $ (not . null) [() | Put _ <- x]
    classify "PutLit" $ (not . null) [() | PutLit _ <- x]

    tripping
      (S (evalProgram x))
      (RW . fromStrictStateT . unS)
      (Just . S . toStrictStateT . unRW)

    (`Strict.runState` 0) (evalProgram x)
      ===
      (`Strict.runState` 0) (roundtrip (evalProgram x))

tests :: IO Bool
tests =
  checkParallel $$(discover)
