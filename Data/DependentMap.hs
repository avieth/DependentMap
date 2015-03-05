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

  , DMapFunction

  , module Data.Typeable

  ) where

import Data.Typeable

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
     , Typeable (DMapFunction t a)
     )
  => k a
  -> v (DMapFunction t a)
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

dFoldWithKey
  :: forall t k v r .
     (
     )
  => (forall k v a . k a -> v (DMapFunction t a) -> r -> r)
  -> r
  -> DMap t k v
  -> r
dFoldWithKey f b dmap = case dmap of
  DMapNil -> b
  DMapCons key val rest -> dFoldWithKey f (f key val b) rest
