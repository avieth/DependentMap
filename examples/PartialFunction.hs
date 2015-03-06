{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Applicative
import Control.Monad.Free

import Data.IORef

-- Just for an example
import qualified Data.Map as M

data Access = ReadOnly | ReadWrite

data MType = MInjective | MNotInjective

data Manifest :: MType -> Access -> * -> * -> * where
  ManifestN :: (a -> Maybe b) -> Manifest MNotInjective ReadWrite a b
  ManifestI :: (a -> Maybe b) -> (b -> Maybe a) -> Manifest MInjective ReadWrite a b

invertManifest :: Manifest MInjective access a b -> Manifest MInjective access b a
invertManifest m = case m of
  ManifestI f g -> ManifestI g f

-- Where to go from here?
-- Well, we must shape that Manifest GADT above... how can we define it so that
-- impure "functions" are accommodated?
-- Keep in mind resource acquisition and release, and transaction handling!
--   acquire :: m (resource, m (), m ()) -- second is rollback, third is release.
-- The problem is when we encounter two terms of the same Manifest, and wish to
-- not re-acquire a resource. Evidently we must have an Eq on Manifest! Or
-- something a lot like it: SameResource :: Manifest -> Manifest -> Prop
-- Yeah! That's it! An implementation-dependent function to indicate whether
-- two manifests can share a resource!

data PartialFunctionN :: Access -> * -> * -> * where
  PFN :: Manifest mtype access a b -> PartialFunctionN access a b
  CPFN :: PartialFunctionN access1 a b -> PartialFunctionN access2 b c -> PartialFunctionN ReadOnly a c

data PartialFunctionI :: Access -> * -> * -> * where
  PFI :: Manifest MInjective access a b -> PartialFunctionI access a b
  CPFI :: PartialFunctionI access1 a b -> PartialFunctionI access2 b c -> PartialFunctionI ReadOnly a c
  IPFI :: PartialFunctionI access a b -> PartialFunctionI access b a

data PartialFunction :: Access -> * -> * -> * where
  Normal :: PartialFunctionN access a b -> PartialFunction access a b
  Injective :: PartialFunctionI access a b -> PartialFunction access a b

-- | Make a normal partial function from an injective one, by dropping the
--   proof of injectivity.
makeN :: PartialFunctionI access a b -> PartialFunctionN access a b
makeN pfi = case pfi of
  PFI f -> PFN f
  CPFI pff pfg -> CPFN (makeN pff) (makeN pfg)
  IPFI pf -> makeN (invertPF pf)

invertPF :: PartialFunctionI access a b -> PartialFunctionI access b a
invertPF pfi = case pfi of
  PFI f -> PFI (invertManifest f)
  CPFI pff pfg -> CPFI (invertPF pfg) (invertPF pff)
  IPFI pf -> pf

(!-) = invertPF

{-
runPF :: PartialFunction a b -> a -> IO (Maybe b)
runPF pf x = case pf of
  Normal pfn -> atN pfn x
  Injective pfi -> atI pfi x

atN :: PartialFunctionN a b -> a -> IO (Maybe b)
atN pfn x = case pfn of
  PFN iof -> iof >>= \f -> return (f x)
  CPFN pf pg -> do
    maybeY <- atN pf x
    case maybeY of 
      Nothing -> return Nothing
      Just y -> atN pg y

atI :: PartialFunctionI a b -> a -> IO (Maybe b)
atI pfi x = case pfi of
  PFI iof _ -> iof >>= \f -> return (f x)
  CPFI pf pg -> do
    maybeY <- atI pf x
    case maybeY of
      Nothing -> return Nothing
      Just y -> atI pg y
  IPFI pf -> atI (invertPF pf) x

(~>) :: PartialFunction a b -> PartialFunction b c -> PartialFunction a c
(~>) pf pg = case pf of
  Normal pfnf -> case pg of
    Normal pfng -> Normal $ CPFN pfnf pfng
    Injective pfig -> Normal $ CPFN pfnf (makeN pfig)
  Injective pfif -> case pg of
    Injective pfig -> Injective $ CPFI pfif pfig
    Normal pfng -> Normal $ CPFN (makeN pfif) pfng

fromPure :: (a -> b) -> PartialFunction a b
fromPure f = Normal (PFN check)
  where
    check = 
  ioref <- newIORef (fmap Just f)
  return $ Normal (PFN ioref)

--fromPureInjective :: (a -> b) -> (b -> a) -> PartialFunction a b
--fromPureInjective f g = Injective (PFI (fmap Just f) (fmap Just g))

fromMap :: Ord a => M.Map a b -> IO (PartialFunction a b)
fromMap map = do
  ioref <- newIORef (\x -> M.lookup x map)
  return $ Normal (PFN ioref)

data M' :: * -> * where
  At :: PartialFunction domain range -> domain -> (Maybe range -> t) -> M' t
  MPure :: t -> M' t

instance Functor M' where
  fmap f x = case x of
    At a b g -> At a b (fmap f g)
    MPure a -> MPure (f a)

-- Our monad for writing queries and assignments.
type M = Free M'

runM :: M a -> IO a
runM = iterM run
  where
    run x = case x of
      MPure m -> m
      At p x f -> (runPF p x) >>= f

at :: PartialFunction domain range -> domain -> M (Maybe range)
at m x = liftF $ At m x id

example = do
  x <- (fromPure not) `at` False
  y <- (fromPure not) `at` True
  z <- (fromMap (M.fromList [("A",False), ("B",False), ("C",True)])) `at` "B"
  return $ (&&) <$> x <*> z
-}
