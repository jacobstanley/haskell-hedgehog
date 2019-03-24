{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
module Test.Example.CCircularBuffer where

import           Foreign.C.Types
import           Hedgehog
import           Hedgehog.C
import qualified Hedgehog.Gen as Gen
import           Hedgehog.Internal.State.TH
import qualified Hedgehog.Range as Range

--import Test.Example.CCircularBuffer.Generated

$(generate defaultConfig {
    configCHeaders =
      ["csrc/circularbuffer/circularbuffer.h"]
  , configCLibrary =
      "csrc/circularbuffer/circularbuffer.dylib"
  })

------------------------------------------------------------------------
-- Commands for csrc/circularbuffer/circularbuffer.h

$(command 'circbuffer_destroy [V])
$(command 'circbuffer_create [G])
$(command 'circbuffer_get [V])
$(command 'circbuffer_put [V,G])
$(command 'circbuffer_size [V])

tests :: IO Bool
tests = do
  loadCLibrary
  checkSequential $$(discover)
