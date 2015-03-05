{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.DependentMap (

    DependentMap

  , empty
  , singleton
  , insert
  , alter
  , lookup
  , delete
  , foldWithKey
  , size

  , DependentMapFunction

  , DependentMapSimple

  , module Data.Typeable

  ) where

import Prelude hiding (lookup)
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

type family DependentMapFunction (t :: *) (a :: *) :: *

-- | A "dependent map" in which the type of keys has a variable parameter, and
--   the type of the values depends upon the parameter of the particular key.
data DependentMap :: * -> (* -> *) -> (* -> *) -> * where
  DependentMapNil :: DependentMap t k v
  DependentMapCons
    :: ( Ord (k a)
       , Typeable a
       , Typeable b
       , b ~ DependentMapFunction t a
       )
    => k a
    -> v b
    -> DependentMap t k v
    -> DependentMap t k v

empty :: DependentMap t k v
empty = DependentMapNil

singleton
  :: forall t k v a b .
     ( Ord (k a)
     , Typeable a
     , Typeable b
     , b ~ DependentMapFunction t a
     )
  => k a
  -> v b
  -> DependentMap t k v
singleton key val = DependentMapCons key val empty

insert
  :: ( Eq (k a)
     , Ord (k a)
     , Typeable a
     , Typeable b
     , b ~ DependentMapFunction t a
     )
  => k a
  -> v b
  -> DependentMap t k v
  -> DependentMap t k v
insert key val dmap = case dmap of
  DependentMapNil -> DependentMapCons key val DependentMapNil
  DependentMapCons key' val' rest -> case heteroEq key key' of
    True -> DependentMapCons key val rest
    False -> DependentMapCons key' val' (insert key val rest)

alter
  :: forall t k v a b .
     ( Ord (k a)
     , Typeable a
     , Typeable b
     , b ~ DependentMapFunction t a
     )
  => (Maybe (v b) -> Maybe (v b))
  -> k a
  -> DependentMap t k v
  -> DependentMap t k v
alter f key dmap = case f (lookup key dmap) of
  Just val -> insert key val dmap
  Nothing -> delete key dmap
{-
alter f key dmap = case lookup key dmap of
  Just val -> case f (Just val) of
    Just val' -> insert key val' dmap
    Nothing -> delete key dmap
  Nothing -> case f Nothing of
    Just val' -> insert key val' dmap
    Nothing -> dmap
-}

lookup
  :: forall t k v a b c .
     ( Eq (k a)
     , Typeable a
     , Typeable b
     , b ~ (DependentMapFunction t a)
     )
  => k a
  -- ^ Will look this up under heterogeneous equality...
  -> DependentMap t k v
  -- ^ ... in this heterogeneous map ...
  -> Maybe (v b)
  -- ^ ... and if a match is found, you get a value and an equality.
lookup key dmap = case dmap of
  DependentMapNil -> Nothing
  -- TODO encapsulate this as a "special eq" or perhaps "heterogeneous eq"
  DependentMapCons key' (val :: v d) rest -> case eqT :: Maybe (d :~: (DependentMapFunction t a)) of
    Just Refl -> if heteroEq key key' then Just val else lookup key rest
    -- ^ Pattern matching on the Refl allows us to use the Match constructor.
    Nothing -> lookup key rest

delete
  :: ( Eq (k a)
     , Typeable a
     )
  => k a
  -> DependentMap t k v
  -> DependentMap t k v
delete key dmap = case dmap of
  DependentMapNil -> DependentMapNil
  DependentMapCons key' _ rest -> if heteroEq key key' then rest else delete key dmap

-- How could a fold possibly work?
-- The provided function has to switch its behaviour based on the type
-- parameter!
-- This attempt is not very useful; all we can use is functions parametrically
-- polymorphic in the parameter!
foldWithKey
  :: forall t k v r .
     (
     )
  => ( forall a b .
       ( Ord (k a)
       , Typeable a
       , Typeable b
       , b ~ DependentMapFunction t a
       )
       => k a
       -> v b
       -> r
       -> r
     )
  -- ^ We're careful to throw everything we know about a and b into the context.
  --   These constraints are just plucked from the DependentMapCons constructor.
  -> r
  -> DependentMap t k v
  -> r
foldWithKey f b dmap = case dmap of
  DependentMapNil -> b
  DependentMapCons key val rest -> foldWithKey f (f key val b) rest

union
  :: forall t k v .
     (
     )
  => DependentMap t k v
  -> DependentMap t k v
  -> DependentMap t k v
union dmapLeft dmapRight = foldWithKey insert dmapLeft dmapRight

size
  :: forall t k v .
     (
     )
  => DependentMap t k v
  -> Int
size dmap = foldWithKey (\_ _ i -> i + 1) 0 dmap

instance Monoid (DependentMap t k v) where
  mempty = empty
  mappend = union

data DependentMapIdentity
type instance DependentMapFunction DependentMapIdentity a = a

type DependentMapSimple = DependentMap DependentMapIdentity
