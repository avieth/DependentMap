{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.DependentMap as DM
import qualified Data.ByteString as BS
import qualified Data.Text as T
import Data.Functor.Identity
import Data.Typeable
import Data.Monoid
import Control.Applicative
import Control.Monad.Free
import Control.Monad.Trans.State
import Control.Monad.IO.Class
import System.IO
import Database.SQLite.Simple
import GHC.Exts (Constraint)

data DErrorMap

type instance DM.DependentMapFunction DErrorMap a = ThingError a

data FixedError = WTF
  deriving (Show, Typeable)

type DErrorValue = Either FixedError

type DErrorKey = Identity


class Thing a where
  type ThingError a :: *

-- This is to be used as a key parameter, so we need not only typeable, but
-- also Ord (and therefore Eq).
data ThingOne = ThingOne Int
  deriving (Typeable, Eq, Ord)

data ThingOneError = OhNo
  deriving (Show, Typeable)

instance Thing ThingOne where
  type ThingError ThingOne = ThingOneError

data ThingTwo = ThingTwo String
  deriving (Typeable, Eq, Ord)

data ThingTwoError = Yikes
  deriving (Show, Typeable)

instance Thing ThingTwo where
  type ThingError ThingTwo = ThingTwoError


exampleDM :: DM.DependentMap DErrorMap DErrorKey DErrorValue
exampleDM =
     DM.singleton (Identity $ ThingOne 1) (Right OhNo)
  <> DM.singleton (Identity $ ThingOne 2) (Left WTF)
  <> DM.singleton (Identity $ ThingTwo "a") (Left WTF)
  <> DM.singleton (Identity $ ThingTwo "b") (Right Yikes)
  <> DM.singleton (Identity $ ThingTwo "c") (Left WTF)
  <> DM.empty


data Resource r where
  Resource :: r -> (r -> IO ()) -> Resource r
  -- ^ The resource, and an action to release it (must never fail).

resource :: Resource r -> r
resource (Resource r _) = r

release :: Resource r -> IO ()
release (Resource r rel) = rel r

-- | A ResourceDescriptor determines a kind of resource, and describes how
--   to produce one.
--   We demand Ord because we want the descriptor to uniquely determine a
--   resource and to be able to use descriptors in efficient maps. Two
--   descriptors must be equal if and only if the resources they would
--   produce (via makeResource) would be observationally identical!
--   The ordering is irrelevant, so long as it's really a total order.
--   Typeable is needed so that we can use it in a dependent map.
class (Ord rd, Typeable rd) => ResourceDescriptor rd where
  type ResourceType rd :: *
  makeResource :: rd -> IO (Resource (ResourceType rd))

-- TODO proper Eq instance demands that we not use string equality, but
-- file path equality, so that two FileDercriptors are equal precisely
-- when their FilePaths pick out the same resource.
data FileDescriptor = FD FilePath
  deriving (Eq, Ord, Typeable)

instance ResourceDescriptor FileDescriptor where
  type ResourceType FileDescriptor = Handle
  makeResource (FD fp) = do
    h <- openFile fp ReadMode
    return $ Resource h hClose

data PureDescriptor = PD
  deriving (Eq, Ord, Typeable)

instance ResourceDescriptor PureDescriptor where
  type ResourceType PureDescriptor = ()
  makeResource PD = return $ Resource () return

data SQLiteDescriptor = SQLD String
  deriving (Eq, Ord, Typeable)

instance ResourceDescriptor SQLiteDescriptor where
  type ResourceType SQLiteDescriptor = Connection
  makeResource (SQLD str) = do
    conn <- open str
    return $ Resource conn close

type DResourceKey = Identity

data DResourceMap
type instance DM.DependentMapFunction DResourceMap a = ResourceType a

exampleRM :: IO (DM.DependentMap DResourceMap DResourceKey Resource)
exampleRM = do
  let fd1 = FD "./test1.txt"
  let fd2 = FD "./test2.txt"
  let sql1 = SQLD "./test1.db"
  let sql2 = SQLD "./test2.db"
  r1 <- makeResource fd1
  r2 <- makeResource fd2
  r3 <- makeResource sql1
  r4 <- makeResource sql2
  return $
         DM.singleton (Identity fd1) r1
      <> DM.singleton (Identity fd2) r2
      <> DM.singleton (Identity sql1) r3
      <> DM.singleton (Identity sql2) r4
      <> DM.empty

releaseAll :: DM.DependentMap DResourceMap DResourceKey Resource -> IO ()
releaseAll dmap = DM.foldWithKey releaseOne (return ()) dmap
  where
    releaseOne _ res io = io >> release res

-- DEFINITION OF MANIFEST CLASSES

data Access = ReadOnly | ReadWrite
data MType = MInjective | MNotInjective

type family AccessConstraint m (a :: Access) :: Constraint where
  AccessConstraint m ReadOnly = ()
  AccessConstraint m ReadWrite = ManifestWrite m

class Manifest (a :: MType -> Access -> * -> * -> *) where
  type ManifestResourceDescriptor a :: *
  resourceDescriptor :: a mtype access domain range -> ManifestResourceDescriptor a
  -- The actual "low-level" domain and range types can depend upon
  -- the "high-level" domain and range.
  type ManifestDomainType a domain range :: *
  type ManifestRangeType a domain range :: *
  type ManifestDomainConstraint a domain range :: Constraint
  type ManifestRangeConstraint a domain range :: Constraint
  mdomainDump
    :: ManifestDomainConstraint a domain range
    => a mtype access domain range
    -> domain
    -> ManifestDomainType a domain range
  mrangePull
    :: ManifestRangeConstraint a domain range
    => a mtype access domain range
    -> ManifestRangeType a domain range
    -> Maybe range

class Manifest a => ManifestRead a where
  mget
    :: (
       )
    => a mtype access domain range
    -> ResourceType (ManifestResourceDescriptor a)
    -> ManifestDomainType a domain range
    -> IO (Maybe (ManifestRangeType a domain range))

class Manifest a => ManifestWrite a where
  mrangeDump
    :: ManifestRangeConstraint a domain range
    => a mtype access domain range
    -> range
    -> ManifestRangeType a domain range
  mset
    :: (
       )
    => a mtype ReadWrite domain range
    -> ResourceType (ManifestResourceDescriptor a)
    -> ManifestDomainType a domain range
    -> Maybe (ManifestRangeType a domain range)
    -> IO ()

class Manifest a => ManifestInjective a where
  minvert 
    :: ( mtype ~ MInjective
       )
    => a mtype access domain range
    -> a mtype access range domain

data PureManifest mtype access a b where
  PureManifest :: (a -> Maybe b) -> PureManifest MNotInjective ReadOnly a b

instance Manifest PureManifest where
  type ManifestResourceDescriptor PureManifest = PureDescriptor
  resourceDescriptor _ = PD
  type ManifestDomainType PureManifest domain range = domain
  type ManifestRangeType PureManifest domain range = range
  type ManifestDomainConstraint PureManifest domain range = ()
  type ManifestRangeConstraint PureManifest domain range = ()
  mdomainDump = const id
  mrangePull = const Just

instance ManifestRead PureManifest where
  mget (PureManifest f) () x = return $ f x


data PartialFunctionN :: Access -> * -> * -> * where
  PFN
    :: ( ManifestRead m
       , ResourceDescriptor (ManifestResourceDescriptor m)
       , ManifestDomainConstraint m domain range
       , ManifestRangeConstraint m domain range
       , AccessConstraint m access
       )
    => m mtype access domain range
    -> PartialFunctionN access domain range
  CPFN
    :: PartialFunctionN access1 domain range1
    -> PartialFunctionN access2 range1 range
    -> PartialFunctionN ReadOnly domain range
    -- ^ Always ReadOnly; you can only update an individual manifest, not
    --   a composition.

data PartialFunctionI :: Access -> * -> * -> * where
  PFI
    :: ( ManifestRead m
       , ResourceDescriptor (ManifestResourceDescriptor m)
       , ManifestDomainConstraint m domain range
       , ManifestRangeConstraint m domain range
       , ManifestDomainConstraint m range domain
       , ManifestRangeConstraint m range domain
       -- ^ We need the range and domain constraints on both sides, since we
       --   may invert!
       , AccessConstraint m access
       , ManifestInjective m
       )
    => m MInjective access domain range
    -> PartialFunctionI access domain range
  CPFI
    :: PartialFunctionI access1 domain range1
    -> PartialFunctionI access2 range1 range
    -> PartialFunctionI ReadOnly domain range
  IPFI
    :: PartialFunctionI access domain range
    -> PartialFunctionI access range domain

data PartialFunction :: Access -> * -> * -> * where
  Normal :: PartialFunctionN access a b -> PartialFunction access a b
  Injective :: PartialFunctionI access a b -> PartialFunction access a b

makeN :: PartialFunctionI access domain range -> PartialFunctionN access domain range
makeN pfi = case pfi of
  PFI manifest -> PFN manifest
  CPFI pfiA pfiB -> CPFN (makeN pfiA) (makeN pfiB)
  IPFI pfi' -> makeN (pfInvert pfi')

compose
  :: PartialFunction access1 domain range1
  -> PartialFunction access2 range1 range
  -> PartialFunction ReadOnly domain range
compose pfA pfB = case pfA of
  Normal pfnA -> case pfB of
    Normal pfnB -> Normal $ CPFN pfnA pfnB
    Injective pfiB -> Normal $ CPFN pfnA (makeN pfiB)
  Injective pfiA -> case pfB of
    Normal pfnB -> Normal $ CPFN (makeN pfiA) pfnB
    Injective pfiB -> Injective $ CPFI pfiA pfiB

(~>) = compose

pfInvert :: PartialFunctionI access domain range -> PartialFunctionI access range domain
pfInvert pf = case pf of
  PFI manifest -> PFI $ minvert manifest
  CPFI pfA pfB -> CPFI (pfInvert pfB) (pfInvert pfA)
  IPFI pf' -> pf'

runGet
  :: ( ManifestRead manifest
     , ResourceDescriptor (ManifestResourceDescriptor manifest)
     , ManifestDomainConstraint manifest domain range
     , ManifestRangeConstraint manifest domain range
     )
  => manifest mtype access domain range
  -> domain
  -> StateT (DM.DependentMap DResourceMap DResourceKey Resource) IO (Maybe range)
runGet manifest x = do
    dmap <- get
    rsrc <- case DM.lookup (Identity $ resourceDescriptor manifest) dmap of
      Nothing -> do
          r <- liftIO $ makeResource (resourceDescriptor manifest)
          put $ DM.insert (Identity $ resourceDescriptor manifest) r dmap
          return r
      Just r -> return r
    y <- liftIO $ mget manifest (resource rsrc) (mdomainDump manifest x)
    return $ case y of
      Nothing -> Nothing
      Just y' -> mrangePull manifest y'

runSet
  :: ( ManifestWrite manifest
     , ResourceDescriptor (ManifestResourceDescriptor manifest)
     , ManifestDomainConstraint manifest domain range
     , ManifestRangeConstraint manifest domain range
     )
  => manifest mtype ReadWrite domain range
  -> domain
  -> Maybe range
  -> StateT (DM.DependentMap DResourceMap DResourceKey Resource) IO ()
runSet manifest x y = do
    dmap <- get
    rsrc <- case DM.lookup (Identity $ resourceDescriptor manifest) dmap of
      Nothing -> do
          r <- liftIO $ makeResource (resourceDescriptor manifest)
          put $ DM.insert (Identity $ resourceDescriptor manifest) r dmap
          return r
      Just r -> return r
    let y' = mrangeDump manifest <$> y
    liftIO $ mset manifest (resource rsrc) (mdomainDump manifest x) y'

runPFGet
  :: (
     )
  => PartialFunction access domain range
  -> domain
  -> StateT (DM.DependentMap DResourceMap DResourceKey Resource) IO (Maybe range)
runPFGet pf x = case pf of
  Normal (PFN manifest) -> runGet manifest x
  Injective (PFI manifest) -> runGet manifest x
  Normal (CPFN pfA pfB) -> do
    y <- runPFGet (Normal pfA) x
    case y of
      Nothing -> return Nothing
      Just y' -> runPFGet (Normal pfB) y'
  Injective (CPFI pfA pfB) -> do
    y <- runPFGet (Injective pfA) x
    case y of
      Nothing -> return Nothing
      Just y' -> runPFGet (Injective pfB) y'
  Injective (IPFI pfA) -> runPFGet (Injective $ pfInvert pfA) x

runPFSet
  :: (
     )
  => PartialFunction ReadWrite domain range
  -> domain
  -> Maybe range
  -> StateT (DM.DependentMap DResourceMap DResourceKey Resource) IO ()
runPFSet pf x y = case pf of
  Normal (PFN manifest) -> runSet manifest x y
  Injective (PFI manifest) -> runSet manifest x y
  Injective (IPFI pf') -> runPFSet (Injective $ pfInvert pf') x y
  -- Other cases ruled out by Access type.

data M' t where
  MPure :: t -> M' t
  MAt
    :: (
       )
    => PartialFunction access domain range
    -> domain
    -> (Maybe range -> t)
    -> M' t
  MAssign
    :: (
       )
    => PartialFunction ReadWrite domain range
    -> domain
    -> Maybe range
    -> t
    -> M' t

instance Functor M' where
  fmap f m' = case m' of
    MPure x -> MPure $ f x
    MAt manifest x g -> MAt manifest x (fmap f g)
    MAssign manifest x y next -> MAssign manifest x y (f next)

type M = Free M'

at :: PartialFunction access domain range -> domain -> M (Maybe range)
at pf x = liftF (MAt pf x id)

assign :: PartialFunction ReadWrite domain range -> domain -> Maybe range -> M ()
assign pf x y = liftF (MAssign pf x y ())

infixr 9 .:=

(.:=) = assign

runM :: M a -> StateT (DM.DependentMap DResourceMap DResourceKey Resource) IO a
runM term = iterM run term >>= finalize
  where

    finalize x = do
      dmap <- get
      liftIO $ releaseAll dmap
      return x

    run :: M' (StateT (DM.DependentMap DResourceMap DResourceKey Resource) IO a)
        -> StateT (DM.DependentMap DResourceMap DResourceKey Resource) IO a
    run m' = case m' of
      MPure action -> action
      MAt pf x nextAction -> runPFGet pf x >>= nextAction
      MAssign pf x y next -> runPFSet pf x y >> next

-- Moving forward: we need a custom monad which is
--   IO
--   with exceptions
--   with state
--   with "finalizer" which can use that state.

-- We should now be equipped to interpret the M monad from other examples,
-- without assignment.

data SQLiteManifest mtype access domain range where
  SQLiteManifest :: SQLiteDescriptor -> String -> SQLiteManifest MNotInjective ReadOnly domain range

class TextSerializable a where
  textSerialize :: a -> T.Text
  textDeserialize :: T.Text -> Maybe a

instance TextSerializable [Char] where
  textSerialize = T.pack
  textDeserialize = Just . T.unpack

instance Manifest SQLiteManifest where
  type ManifestResourceDescriptor SQLiteManifest = SQLiteDescriptor
  resourceDescriptor (SQLiteManifest sqld _) = sqld
  type ManifestDomainType SQLiteManifest domain range = T.Text
  type ManifestRangeType SQLiteManifest domain range = T.Text
  type ManifestDomainConstraint SQLiteManifest domain range = TextSerializable domain
  type ManifestRangeConstraint SQLiteManifest domain range = TextSerializable range
  mdomainDump _ = textSerialize
  mrangePull _ = textDeserialize

instance ManifestRead SQLiteManifest where
  mget (SQLiteManifest _ tableName) conn key = do
    y <- query conn "SELECT \"2\" FROM test WHERE \"1\"=?" (Only key) :: IO [Only T.Text]
    return $ case y of
      [] -> Nothing
      (y' : _) -> Just (fromOnly y')

pm :: PureManifest MNotInjective ReadOnly Bool String
pm = PureManifest (\x -> Just $ if x then "foo" else "bar")

sq :: SQLiteManifest MNotInjective ReadOnly String String
sq = SQLiteManifest (SQLD "./test1.db") "test"

pf1 = Normal $ PFN pm

pf2 = Normal $ PFN sq

exampleTerm1 :: M (Maybe String)
exampleTerm1 = do
  foo <- pf1 `at` True
  bar <- pf2 `at` "foo"
  return $ (++) <$> foo <*> bar

exampleTerm2 :: M (Maybe String)
exampleTerm2 = (pf1 ~> pf2) `at` False
