{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Example.StateT where

import           Control.Monad.State.Class (MonadState(..))
import qualified Control.Monad.State.Strict as Strict

import           Hedgehog hiding (Var)
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Gen as Gen

import qualified Hedgehog.Internal.Gen as Gen (toTree, fromTree)
import qualified Hedgehog.Internal.Tree as Tree (render)


genNum :: MonadGen m => (forall n. MonadGen n => n Int -> n a) -> m a
genNum =
  Gen.cycle [
      Gen.int (Range.constant 0 2)
    , Gen.int (Range.constant 3 5)
    , Gen.int (Range.constant 6 8)
    ]

gen4 :: MonadGen m => m (Int, Int, Int, Int)
gen4 =
  genNum $ \gen ->
    (,,,)
      <$> gen
      <*> gen
      <*> gen
      <*> gen

prop_cycle :: Property
prop_cycle =
  property $ do
    tree <- forAllWith (Tree.render . fmap show) (Gen.toTree gen4)
    _ <- forAll (Gen.fromTree tree)
    assert False

data Exp =
    Var Int
  | Add Exp Exp
  | Mul Exp Exp deriving (Eq, Show)

nextFresh :: MonadState Int m => m Int
nextFresh = do
  x <- get
  put (x + 1)
  pure x

genExp :: (MonadGen m, MonadState Int m) => m Exp
genExp =
  Gen.recursive Gen.choice [
      Var <$> nextFresh
    ] [
      Add <$> genExp <*> genExp
    , Mul <$> genExp <*> genExp
    ]

size :: Exp -> Int
size = \case
  Var _ ->
    1
  Add x y ->
    size x + size y
  Mul x y ->
    size x + size y

rendersPrec :: Int -> Exp -> String -> String
rendersPrec p = \case
  Var n ->
    showString "x" .
    showString (show n)
  Add x y ->
    showParen (p > 6) $
      rendersPrec 6 x .
      showString " + " .
      rendersPrec 6 y
  Mul x y ->
    showParen (p > 7) $
      rendersPrec 7 x .
      showString " * " .
      rendersPrec 7 y

render :: Exp -> String
render x =
  rendersPrec 0 x ""

prop_fresh :: Property
prop_fresh =
  property $ do
    let
      gen =
        Strict.evalStateT genExp 0

    tree <- forAllWith (Tree.render . fmap render) (Gen.toTree gen)
    expr <- forAllWith render (Gen.fromTree tree)
    assert $ size expr < 2

tests :: IO Bool
tests =
  checkParallel $$(discover)
