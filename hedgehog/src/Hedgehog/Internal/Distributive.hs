{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
module Hedgehog.Internal.Distributive (
    MonadTransDistributive(..)

  , fromStrictStateT
  , toStrictStateT

  , fromLazyStateT
  , toLazyStateT

  , fromStrictRWST
  , toStrictRWST

  , fromLazyRWST
  , toLazyRWST
  ) where

import           Control.Monad (join)
import           Control.Monad.Morph (MFunctor(..))
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Identity (IdentityT(..))
import           Control.Monad.Trans.Except (ExceptT(..), runExceptT)
import           Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Control.Monad.Trans.RWS.Lazy as Lazy (RWST(..))
import qualified Control.Monad.Trans.RWS.Strict as Strict (RWST(..))
import           Control.Monad.Trans.Reader (ReaderT(..))
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Strict as Strict

import           Data.Bifunctor (Bifunctor(..))
import           Data.Maybe (fromMaybe)
import           Data.Monoid (Last(..))

import           GHC.Exts (Constraint)

-- NOTE: Replace use of Proxy with TypeApplications when we drop 7.10 support.

------------------------------------------------------------------------
-- * MonadTransDistributive

class MonadTransDistributive g where
  type Transformer
    (f :: (* -> *) -> * -> *)
    (g :: (* -> *) -> * -> *)
    (m :: * -> *) :: Constraint

  type Transformer f g m = (
      Monad m
    , Monad (f m)
    , Monad (g m)
    , Monad (f (g m))
    , MonadTrans f
    , MFunctor f
    )

  -- | Distribute one monad transformer over another.
  --
  distributeT :: Transformer f g m => g (f m) a -> f (g m) a

instance MonadTransDistributive IdentityT where
  distributeT m =
    lift . IdentityT . pure =<< hoist lift (runIdentityT m)

instance MonadTransDistributive MaybeT where
  distributeT m =
    lift . MaybeT . pure =<< hoist lift (runMaybeT m)

instance MonadTransDistributive (ExceptT x) where
  distributeT m =
    lift . ExceptT . pure =<< hoist lift (runExceptT m)

instance MonadTransDistributive (ReaderT r) where
  distributeT m =
    join . lift . ReaderT $ \r ->
      pure . hoist lift $ runReaderT m r

instance Monoid w => MonadTransDistributive (Lazy.WriterT w) where
  distributeT m =
    lift . Lazy.WriterT . pure =<< hoist lift (Lazy.runWriterT m)

instance Monoid w => MonadTransDistributive (Strict.WriterT w) where
  distributeT m = do
    lift . Strict.WriterT . pure =<< hoist lift (Strict.runWriterT m)

instance MonadTransDistributive (Lazy.StateT s) where
  type Transformer f (Lazy.StateT s) m = (
      Monad m
    , Monad (f m)
    , Monad (f (Lazy.WriterT (Last s) m))
    , Monad (f (ReaderT s (Lazy.WriterT (Last s) m)))
    , MonadTrans f
    , MFunctor f
    )
  distributeT =
    hoist toLazyStateT .
    distributeT .
    hoist distributeT .
    fromLazyStateT

instance MonadTransDistributive (Strict.StateT s) where
  type Transformer f (Strict.StateT s) m = (
      Monad m
    , Monad (f m)
    , Monad (f (Strict.WriterT (Last s) m))
    , Monad (f (ReaderT s (Strict.WriterT (Last s) m)))
    , MonadTrans f
    , MFunctor f
    )
  distributeT =
    hoist toStrictStateT .
    distributeT .
    hoist distributeT .
    fromStrictStateT

instance Monoid w => MonadTransDistributive (Lazy.RWST r w s) where
  type Transformer f (Lazy.RWST r w s) m = (
      Monad m
    , Monad (f m)
    , Monad (f (Lazy.WriterT (Last s, w) m))
    , Monad (f (ReaderT (r, s) (Lazy.WriterT (Last s, w) m)))
    , MonadTrans f
    , MFunctor f
    )
  distributeT =
    hoist toLazyRWST .
    distributeT .
    hoist distributeT .
    fromLazyRWST

instance Monoid w => MonadTransDistributive (Strict.RWST r w s) where
  type Transformer f (Strict.RWST r w s) m = (
      Monad m
    , Monad (f m)
    , Monad (f (Strict.WriterT (Last s, w) m))
    , Monad (f (ReaderT (r, s) (Strict.WriterT (Last s, w) m)))
    , MonadTrans f
    , MFunctor f
    )
  distributeT =
    hoist toStrictRWST .
    distributeT .
    hoist distributeT .
    fromStrictRWST

------------------------------------------------------------------------
-- StateT s <-> ReaderT s (WriterT (Last s))

fromLazyStateT :: Functor m => Lazy.StateT s m a -> ReaderT s (Lazy.WriterT (Last s) m) a
fromLazyStateT =
  let
    mkWriter f s = do
      Lazy.WriterT (second (Last . Just) <$> f s)
  in
    ReaderT . mkWriter . Lazy.runStateT

toLazyStateT :: Functor m => ReaderT s (Lazy.WriterT (Last s) m) a -> Lazy.StateT s m a
toLazyStateT =
  let
    runWriter f s =
      second (fromMaybe s . getLast) <$> Lazy.runWriterT (f s)
  in
    Lazy.StateT . runWriter . runReaderT

fromStrictStateT :: Functor m => Strict.StateT s m a -> ReaderT s (Strict.WriterT (Last s) m) a
fromStrictStateT =
  let
    mkWriter f s = do
      Strict.WriterT (second (Last . Just) <$> f s)
  in
    ReaderT . mkWriter . Strict.runStateT

toStrictStateT :: Functor m => ReaderT s (Strict.WriterT (Last s) m) a -> Strict.StateT s m a
toStrictStateT =
  let
    runWriter f s =
      second (fromMaybe s . getLast) <$> Strict.runWriterT (f s)
  in
    Strict.StateT . runWriter . runReaderT

------------------------------------------------------------------------
-- RWST r w s <-> ReaderT s (WriterT (Last s))

pack :: (r, s, w) -> (r, (Last s, w))
pack (r, s, w) =
  (r, (Last (Just s), w))

unpack :: s -> (r, (Last s, w)) -> (r, s, w)
unpack s0 (r, (s, w)) =
  (r, fromMaybe s0 (getLast s), w)

fromLazyRWST :: Functor m => Lazy.RWST r w s m a -> ReaderT (r, s) (Lazy.WriterT (Last s, w) m) a
fromLazyRWST =
  let
    mkWriter f s =
      Lazy.WriterT (pack <$> uncurry f s)
  in
    ReaderT . mkWriter . Lazy.runRWST

toLazyRWST :: Functor m => ReaderT (r, s) (Lazy.WriterT (Last s, w) m) a -> Lazy.RWST r w s m a
toLazyRWST =
  let
    runWriter :: Functor m => ((r, s) -> Lazy.WriterT (Last s, w) m a) -> r -> s -> m (a, s, w)
    runWriter f r s =
      unpack s <$> Lazy.runWriterT (f (r, s))
  in
    Lazy.RWST . runWriter . runReaderT

fromStrictRWST :: Functor m => Strict.RWST r w s m a -> ReaderT (r, s) (Strict.WriterT (Last s, w) m) a
fromStrictRWST =
  let
    mkWriter f s =
      Strict.WriterT (pack <$> uncurry f s)
  in
    ReaderT . mkWriter . Strict.runRWST

toStrictRWST :: Functor m => ReaderT (r, s) (Strict.WriterT (Last s, w) m) a -> Strict.RWST r w s m a
toStrictRWST =
  let
    runWriter :: Functor m => ((r, s) -> Strict.WriterT (Last s, w) m a) -> r -> s -> m (a, s, w)
    runWriter f r s =
      unpack s <$> Strict.runWriterT (f (r, s))
  in
    Strict.RWST . runWriter . runReaderT
