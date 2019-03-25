{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Example.CCircularBuffer where

import           Control.Monad (join)
import           Control.Monad.IO.Class (MonadIO(..))
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (listToMaybe)
import           Foreign.C.Types
import           Hedgehog
import           Hedgehog.C
import qualified Hedgehog.Gen as Gen
import           Hedgehog.Internal.State.TH
import qualified Hedgehog.Range as Range

$(generate defaultConfig {
    configCHeaders =
      ["csrc/circularbuffer/circularbuffer.h"]
  , configCLibrary =
      "csrc/circularbuffer/circularbuffer.dylib"
  })

data Buffer a =
  Buffer {
      bufferSize :: Int
    , bufferData :: [a]
    } deriving (Eq, Ord, Show)

bufferNew :: Int -> Buffer a
bufferNew n =
  Buffer n []

bufferPut :: a -> Buffer a -> Buffer a
bufferPut x (Buffer n xs) =
  Buffer n . reverse . List.take n . reverse $ xs ++ [x]

bufferNext :: Buffer a -> Maybe a
bufferNext (Buffer _n xs) =
  listToMaybe xs

bufferLast :: Buffer a -> Maybe a
bufferLast (Buffer _n xs) =
  listToMaybe (reverse xs)

bufferDrop :: Buffer a -> Buffer a
bufferDrop (Buffer n xs) =
  Buffer n (drop 1 xs)

bufferGet :: Buffer a -> Maybe (a, Buffer a)
bufferGet (Buffer n xs0) =
  case xs0 of
    [] ->
      Nothing
    x : xs ->
      Just (x, Buffer n xs)

data State v =
  State {
      stateBuffers :: Map (Var CircularBuffer v) (Buffer Int)
    }

initialState :: State v
initialState =
  State Map.empty

modify :: Ord k => k -> (v -> Maybe (a, v)) -> Map k v -> Maybe (a, Map k v)
modify k f kvs = do
  v0 <- Map.lookup k kvs
  (x, v1) <- f v0
  pure (x, Map.insert k v1 kvs)

-- Commands for csrc/circularbuffer/circularbuffer.h

$(command "circbuffer_destroy"
  [t| Var CircularBuffer -> IO () |]
  [e| c_circbuffer_destroy |])

$(command "circbuffer_create"
  [t| CInt -> IO CircularBuffer |]
  [e| c_circbuffer_create |])

circbuffer_create :: MonadIO m => Command Gen m State
circbuffer_create =
  let
    gen _ =
      Just $
        Circbuffer_create <$> Gen.integral (Range.linear 1 20)
  in
    circbuffer_createFrom gen [
        Update $ \state (Circbuffer_create n) out ->
          state {
              stateBuffers =
                Map.insert out (bufferNew (fromIntegral n)) (stateBuffers state)
            }

      , Ensure $ \state0 _state1 (Circbuffer_create _n) out -> do
          annotateShow out
          annotateShow (stateBuffers state0)
          assert $
            not (Map.member (Var (Concrete out)) (stateBuffers state0))
      ]

$(command "circbuffer_get"
  [t| Var CircularBuffer -> IO CInt |]
  [e| c_circbuffer_get |])

circbuffer_get :: MonadIO m => Command Gen m State
circbuffer_get =
  let
    gen s =
      case Map.toList (stateBuffers s) of
        [] ->
          Nothing
        xs ->
          Just $
            Circbuffer_get <$> Gen.element (fmap fst xs)
  in
    circbuffer_getFrom gen [
        Require $ \state (Circbuffer_get ptr) ->
          case Map.lookup ptr (stateBuffers state) of
            Nothing ->
              False
            Just buffer ->
              length (bufferData buffer) > 0

      , Update $ \state0 (Circbuffer_get ptr) _out ->
          state0 {
              stateBuffers =
                Map.adjust bufferDrop ptr (stateBuffers state0)
            }

      , Ensure $ \state0 _state1 (Circbuffer_get ptr) out ->
          let
            next :: Maybe Int
            next =
              join . fmap bufferNext . Map.lookup ptr $ stateBuffers state0
          in
            next === Just (fromIntegral out)
      ]

$(command "circbuffer_put"
  [t| Var CircularBuffer -> CInt -> IO () |]
  [e| c_circbuffer_put |])

circbuffer_put :: MonadIO m => Command Gen m State
circbuffer_put =
  let
    gen s =
      case Map.toList (stateBuffers s) of
        [] ->
          Nothing
        xs ->
          Just $
            Circbuffer_put
              <$> Gen.element (fmap fst xs)
              <*> Gen.integral (Range.linear 0 100)
  in
    circbuffer_putFrom gen [
        Require $ \state (Circbuffer_put ptr _) ->
          Map.member ptr (stateBuffers state)

      , Update $ \state0 (Circbuffer_put ptr x) _out ->
          state0 {
              stateBuffers =
                Map.adjust (bufferPut (fromIntegral x)) ptr (stateBuffers state0)
            }

      , Ensure $ \_state0 state1 (Circbuffer_put ptr x) _out ->
          let
            last_ :: Maybe Int
            last_ =
              join . fmap bufferLast . Map.lookup ptr $ stateBuffers state1
          in
            last_ === Just (fromIntegral x)
      ]

$(command "circbuffer_size"
  [t| Var CircularBuffer -> IO CInt |]
  [e| c_circbuffer_size |])

------------------------------------------------------------------------

prop_registry_sequential :: Property
prop_registry_sequential =
  property $ do
    actions <- forAll $
      Gen.sequential (Range.linear 1 100) initialState [
          circbuffer_create
        , circbuffer_get
        , circbuffer_put
        ]

    -- FIXME cleanup buffers? ResourceT?
    executeSequential initialState actions

tests :: IO Bool
tests = do
  loadCLibrary
  checkSequential $$(discover)
