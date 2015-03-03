{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.DependentMap as DM
import Data.Functor.Identity
import Data.Typeable
import Data.Monoid
import Control.Applicative
import Control.Monad.Free
import Control.Monad.Trans.State
import Control.Monad.IO.Class
import System.IO
import Database.SQLite.Simple

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

class Manifest a where
  type ManifestResourceDescriptor a :: *
  resourceDescriptor :: a domain range -> ManifestResourceDescriptor a
  mget :: a domain range -> ResourceType (ManifestResourceDescriptor a) -> domain -> IO (Maybe range)

data PureManifest a b = PureManifest (a -> Maybe b)

instance Manifest PureManifest where
  type ManifestResourceDescriptor PureManifest = PureDescriptor
  resourceDescriptor _ = PD
  mget (PureManifest f) () x = return $ f x

data M' t where
  MPure :: t -> M' t
  MAt
    :: ( Manifest m
       , ResourceDescriptor (ManifestResourceDescriptor m)
       )
    => m domain range -> domain -> (Maybe range -> t) -> M' t

instance Functor M' where
  fmap f m' = case m' of
    MPure x -> MPure $ f x
    MAt manifest x g -> MAt manifest x (fmap f g)

type M = Free M'

at
  :: ( Manifest m
     , ResourceDescriptor (ManifestResourceDescriptor m)
     )
  => m domain range
  -> domain
  -> M (Maybe range)
at m d = liftF (MAt m d id)

exampleTerm :: M (Maybe String)
exampleTerm = do
  foo <- (PureManifest (\x -> Just $ show x) :: PureManifest Bool String) `at` True
  bar <- (PureManifest (\x -> Just $ x ++ "!") :: PureManifest String String) `at` "foo"
  return $ (++) <$> foo <*> bar

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
      MPure io -> io
      MAt manifest x next -> do
        dmap <- get
        rsrc <- case DM.lookup (Identity $ resourceDescriptor manifest) dmap of
          Nothing -> do
              r <- liftIO $ makeResource (resourceDescriptor manifest)
              put $ DM.insert (Identity $ resourceDescriptor manifest) r dmap
              return r
          Just r -> return r
        y <- liftIO $ mget manifest (resource rsrc) x
        next y

-- Moving forward: we need a custom monad which is
--   IO
--   with exceptions
--   with state
--   with "finalizer" which can use that state.

-- We should now be equipped to interpret the M monad from other examples,
-- without assignment.

{-
data SQLiteManifest = SQLiteManifest SQLiteDescriptor String

instance Manifest SQLiteManifest where
  type ManifestResourceDescriptor SQLiteManifest = SQLiteDescriptor
  resourceDescriptor (SQLiteManifest sqld _) = sqld
  mget (SQLiteManifest _ tableName) conn x = do
    y <- query conn "SELECT \"2\" FROM ? WHERE \"1\"=?" (tableName, x) :: IO [Only t]
    case y of
      [] -> Nothing
      (y' : _) -> Just y'
-}
