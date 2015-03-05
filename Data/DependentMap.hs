{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.DependentMap (

    DMap
  , dEmpty
  , dInsert
  , dLookup
  , dDelete
  , dFoldWithKey
  , dSize

  , DMapFunction

  , module Data.Typeable

  ) where

import Data.Typeable
import Data.Monoid

heteroEq :: forall v a b . (Eq (v a), Typeable a, Typeable b) => v a -> v b -> Bool
heteroEq x y = case eqT :: Maybe (a :~: b) of
  Just Refl -> x == y
  Nothing -> False

-- Like heteroEq, but we give the equality type in case they're equal (in type
-- and in Eq instance).
heteroEq'
  :: forall t a b .
     ( Eq (t a)
     , Typeable a
     , Typeable b
     )
  => t a
  -> t b
  -> Maybe (a :~: b)
heteroEq' x y = case eqT :: Maybe (a :~: b) of
  Just Refl -> if x == y then Just Refl else Nothing
  Nothing -> Nothing

heteroOrd :: forall v a b . (Ord (v a), Typeable a, Typeable b) => v a -> v b -> Ordering
heteroOrd x y = case eqT :: Maybe (a :~: b) of
  Just Refl -> x `compare` y
  Nothing ->  typeRep (Proxy :: Proxy a) `compare` typeRep (Proxy :: Proxy b)

type family DMapFunction (t :: *) (a :: *) :: *

-- | A "dependent map" in which the type of keys has a variable parameter, and
--   the type of the values depends upon the parameter of the particular key.
data DMap :: * -> (* -> *) -> (* -> *) -> * where
  DMapNil :: DMap t k v
  DMapCons
    :: ( Eq (k a)
       , Ord (k a)
       , Typeable a
       , Typeable b
       , b ~ DMapFunction t a
       )
    => k a
    -> v b
    -> DMap t k v
    -> DMap t k v

dEmpty :: DMap t k v
dEmpty = DMapNil

dInsert
  :: ( Eq (k a)
     , Ord (k a)
     , Typeable a
     , Typeable b
     , b ~ DMapFunction t a
     )
  => k a
  -> v b
  -> DMap t k v
  -> DMap t k v
dInsert key val dmap = case dmap of
  DMapNil -> DMapCons key val DMapNil
  DMapCons key' val' rest -> case heteroEq key key' of
    True -> DMapCons key val rest
    False -> DMapCons key' val' (dInsert key val rest)

dLookup
  :: forall t k v a b c .
     ( Eq (k a)
     , Typeable a
     , Typeable b
     , b ~ (DMapFunction t a)
     )
  => k a
  -- ^ Will look this up under heterogeneous equality...
  -> DMap t k v
  -- ^ ... in this heterogeneous map ...
  -> Maybe (v b)
  -- ^ ... and if a match is found, you get a value and an equality.
dLookup key dmap = case dmap of
  DMapNil -> Nothing
  -- TODO encapsulate this as a "special eq" or perhaps "heterogeneous eq"
  DMapCons key' (val :: v d) rest -> case eqT :: Maybe (d :~: (DMapFunction t a)) of
    Just Refl -> if heteroEq key key' then Just val else dLookup key rest
    -- ^ Pattern matching on the Refl allows us to use the Match constructor.
    Nothing -> dLookup key rest

dDelete
  :: ( Eq (k a)
     , Typeable a
     )
  => k a
  -> DMap t k v
  -> DMap t k v
dDelete key dmap = case dmap of
  DMapNil -> DMapNil
  DMapCons key' _ rest -> if heteroEq key key' then rest else dDelete key dmap

-- How could a fold possibly work?
-- The provided function has to switch its behaviour based on the type
-- parameter!
-- This attempt is not very useful; all we can use is functions parametrically
-- polymorphic in the parameter!
dFoldWithKey
  :: forall t k v r .
     (
     )
  => (forall a . k a -> v (DMapFunction t a) -> r -> r)
  -> r
  -> DMap t k v
  -> r
dFoldWithKey f b dmap = case dmap of
  DMapNil -> b
  DMapCons key val rest -> dFoldWithKey f (f key val b) rest

-- The problem: you just don't know what parameters could be used in the map!
-- Yet still the function you give must work on ANY parameter! We have this
-- problem even for the earlier version, without DMapFunction. If your k and
-- v types give enough information, then that's great. If not, then you're
-- out of luck.
dFoldWithKey'
  :: forall t k v r .
     (
     )
  => (forall a . k a -> v (DMapFunction t a) -> r -> r)
  -> r
  -> DMap t k v
  -> r
dFoldWithKey' f b dmap = case dmap of
  DMapNil -> b
  DMapCons key val rest -> dFoldWithKey f (f key val b) rest

-- Another problem: we demand Typeable (DMapFunction t a) FOR EVERY a!!!!
-- Damn...
-- Hm, can't we just take it at insert time, then recover it from pattern
-- matching on DMapCons?

dUnion
  :: forall t k v .
     (
     )
  => DMap t k v
  -> DMap t k v
  -> DMap t k v
dUnion dmapLeft dmapRight = case dmapRight of
  DMapNil -> dmapLeft
  DMapCons key val rest -> dInsert key val (dUnion dmapLeft rest)
-- Interesting: the above works, but the below does not!
--dUnion dmapLeft dmapRight = dFoldWithKey union dmapLeft dmapRight

dSize
  :: forall t k v .
     (
     )
  => DMap t k v
  -> Int
dSize dmap = dFoldWithKey (\_ _ i -> i + 1) 0 dmap

instance Monoid (DMap t k v) where
  mempty = dEmpty
  mappend = dUnion
