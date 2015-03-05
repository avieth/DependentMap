{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Data.DependentMap (

    DMap
  , dEmpty
  , dInsert
  , dLookup
  , dDelete
  , dFold
  , dFoldWithKey
  , module Data.Typeable

  ) where

import Data.Typeable

heteroEq :: forall v a b . (Eq (v a), Typeable a, Typeable b) => v a -> v b -> Bool
heteroEq x y = case eqT :: Maybe (a :~: b) of
  Just Refl -> x == y
  Nothing -> False

heteroOrd :: forall v a b . (Ord (v a), Typeable a, Typeable b) => v a -> v b -> Ordering
heteroOrd x y = case eqT :: Maybe (a :~: b) of
  Just Refl -> x `compare` y
  Nothing ->  typeRep (Proxy :: Proxy a) `compare` typeRep (Proxy :: Proxy b)

-- | A "dependent map" in which the type of keys has a variable parameter, and
--   the type of the values depends upon the parameter of the particular key.
data DMap :: (* -> *) -> (* -> *) -> * where
  DMapNil :: DMap k v
  DMapCons
    :: ( Eq (k a)
       , Ord (k a)
       , Typeable a
       )
    => k a
    -> v a
    -> DMap k v
    -> DMap k v

dEmpty :: DMap k v
dEmpty = DMapNil

dInsert
  :: ( Eq (k a)
     , Ord (k a)
     , Typeable a
     )
  => k a
  -> v a
  -> DMap k v
  -> DMap k v
dInsert key val dmap = case dmap of
  DMapNil -> DMapCons key val DMapNil
  DMapCons key' val' rest -> case heteroEq key key' of
    True -> DMapCons key val rest
    False -> DMapCons key' val' (dInsert key val rest)

dLookup
  :: forall k v a b .
     ( Eq (k a)
     , Typeable a
     , a ~ b
     )
  => k a
  -- ^ Will look this up under heterogeneous equality...
  -> DMap k v
  -- ^ ... in this heterogeneous map ...
  -> Maybe (v b)
  -- ^ ... and if a match is found, you get a value and an equality.
dLookup key dmap = case dmap of
  DMapNil -> Nothing
  -- TODO encapsulate this as a "special eq" or perhaps "heterogeneous eq"
  DMapCons key' (val :: v c) rest -> case eqT :: Maybe (a :~: c) of
    Just Refl -> if heteroEq key key' then Just val else dLookup key rest
    -- ^ Pattern matching on the Refl allows us to use the Match constructor.
    Nothing -> dLookup key rest

dDelete
  :: ( Eq (k a)
     , Typeable a
     )
  => k a
  -> DMap k v
  -> DMap k v
dDelete key dmap = case dmap of
  DMapNil -> DMapNil
  DMapCons key' _ rest -> if heteroEq key key' then rest else dDelete key dmap

dFold
  :: forall k v r .
     (
     )
  => (forall v a . v a -> r -> r)
  -> r
  -> DMap k v
  -> r
dFold f b dmap = case dmap of
  DMapNil -> b
  DMapCons _ val rest -> dFold f (f val b) rest

dFoldWithKey
  :: forall k v r .
     (
     )
  => (forall k v a . k a -> v a -> r -> r)
  -> r
  -> DMap k v
  -> r
dFoldWithKey f b dmap = case dmap of
  DMapNil -> b
  DMapCons key val rest -> dFoldWithKey f (f key val b) rest
