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
import qualified Data.ByteString.Char8 as B8
import qualified Data.Text as T
import Data.String
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

type RollbackEffect r = r -> IO ()
type CommitEffect r = r -> IO ()
type ReleaseEffect r = r -> IO ()

-- | TBD Should we demand commit and rollback for every resource? Some
--   resources are read-only, in which case we wouldn't need these, no?
data Resource r where
  Resource
    :: r
    -> CommitEffect r
    -> RollbackEffect r
    -> ReleaseEffect r
    -> Resource r

resource :: Resource r -> r
resource (Resource r _ _ _) = r

commit :: Resource r -> IO ()
commit (Resource r c _ _) = c r

rollback :: Resource r -> IO ()
rollback (Resource r _ rb _) = rb r

release :: Resource r -> IO ()
release (Resource r _ _ rel) = rel r

-- | A ResourceDescriptor determines a kind of resource, and describes how
--   to produce one.
--   We demand Ord because we want the descriptor to uniquely determine a
--   resource and to be able to use descriptors in efficient maps. Two
--   descriptors must be equal if and only if the resources they would
--   produce (via acquireResource) would be observationally identical!
--   The ordering is irrelevant, so long as it's really a total order.
--   Typeable is needed so that we can use it in a dependent map.
class (Ord rd, Typeable rd) => ResourceDescriptor rd where
  type ResourceType rd :: *
  acquireResource :: rd -> IO (Resource (ResourceType rd))

data PureDescriptor = PD
  deriving (Eq, Ord, Typeable)

instance ResourceDescriptor PureDescriptor where
  type ResourceType PureDescriptor = ()
  acquireResource PD = return $ Resource () commit rollback release
    where
      commit _ = return ()
      rollback _ = return ()
      release _ = return ()

data SQLiteDescriptor = SQLD String
  deriving (Eq, Ord, Typeable)

instance ResourceDescriptor SQLiteDescriptor where
  type ResourceType SQLiteDescriptor = Connection
  acquireResource (SQLD str) = do
      putStrLn $ "acquiring SQLite db " ++ str
      conn <- open str
      execute_ conn "BEGIN TRANSACTION"
      return $ Resource conn commit rollback release
    where
      rollback conn = do
        putStrLn $ "rolling back SQLite transaction " ++ str
        execute_ conn "ROLLBACK TRANSACTION"
      commit conn = do
        putStrLn $ "committing SQLite transaction " ++ str
        execute_ conn "COMMIT TRANSACTION"
      release conn = do
        putStrLn $ "releaseing SQLite db " ++ str
        close conn


type DResourceKey = Identity

data DResourceMap
type instance DM.DependentMapFunction DResourceMap a = ResourceType a

releaseAll :: DM.DependentMap DResourceMap DResourceKey Resource -> IO ()
releaseAll dmap = DM.foldWithKey releaseOne (return ()) dmap
  where
    releaseOne _ res io = io >> release res

-- DEFINITION OF MANIFEST CLASSES

data Access = ReadOnly | ReadWrite
data MType = MInjective | MNotInjective

type family MTypeMeet (m1 :: MType) (m2 :: MType) :: MType where
  MTypeMeet MInjective MInjective = MInjective
  MTypeMeet MNotInjective MInjective = MNotInjective
  MTypeMeet MInjective MNotInjective = MNotInjective
  MTypeMeet MNotInjective MNotInjective = MNotInjective

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
  PureManifestN :: (a -> Maybe b) -> PureManifest MNotInjective ReadOnly a b
  PureManifestI :: (a -> Maybe b) -> (b -> Maybe a) -> PureManifest MInjective ReadOnly a b

pureFunction :: (a -> Maybe b) -> PureManifest MNotInjective ReadOnly a b
pureFunction = PureManifestN

pureInjection :: (a -> Maybe b) -> (b -> Maybe a) -> PureManifest MInjective ReadOnly a b
pureInjection = PureManifestI

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
  mget pm () x = case pm of
    PureManifestN f -> return $ f x
    PureManifestI f _ -> return $ f x

instance ManifestInjective PureManifest where
  minvert pm = case pm of
    PureManifestI f g -> PureManifestI g f

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

data PartialFunction :: MType -> Access -> * -> * -> * where
  Normal :: PartialFunctionN access a b -> PartialFunction MNotInjective access a b
  Injective :: PartialFunctionI access a b -> PartialFunction MInjective access a b

makeN :: PartialFunctionI access domain range -> PartialFunctionN access domain range
makeN pfi = case pfi of
  PFI manifest -> PFN manifest
  CPFI pfiA pfiB -> CPFN (makeN pfiA) (makeN pfiB)
  IPFI pfi' -> makeN (pfInvert pfi')

function
  :: ( ManifestRead m
     , ResourceDescriptor (ManifestResourceDescriptor m)
     , ManifestDomainConstraint m domain range
     , ManifestRangeConstraint m domain range
     , AccessConstraint m access
     )
  => m mtype access domain range
  -> PartialFunction MNotInjective access domain range
function = Normal . PFN

injection
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
  -> PartialFunction MInjective access domain range
injection = Injective . PFI

compose
  :: PartialFunction mtype1 access1 domain range1
  -> PartialFunction mtype2 access2 range1 range
  -> PartialFunction (MTypeMeet mtype1 mtype2) ReadOnly domain range
compose pfA pfB = case pfA of
  Normal pfnA -> case pfB of
    Normal pfnB -> Normal $ CPFN pfnA pfnB
    Injective pfiB -> Normal $ CPFN pfnA (makeN pfiB)
  Injective pfiA -> case pfB of
    Normal pfnB -> Normal $ CPFN (makeN pfiA) pfnB
    Injective pfiB -> Injective $ CPFI pfiA pfiB

(~>) = compose

invert
  :: PartialFunction MInjective access domain range
  -> PartialFunction MInjective access range domain
invert pf = case pf of
  Injective pfi -> Injective $ pfInvert pfi

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
          r <- liftIO $ acquireResource (resourceDescriptor manifest)
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
          r <- liftIO $ acquireResource (resourceDescriptor manifest)
          put $ DM.insert (Identity $ resourceDescriptor manifest) r dmap
          return r
      Just r -> return r
    let y' = mrangeDump manifest <$> y
    liftIO $ mset manifest (resource rsrc) (mdomainDump manifest x) y'

runPFGet
  :: (
     )
  => PartialFunction mtype access domain range
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
  => PartialFunction mtype ReadWrite domain range
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
    => PartialFunction mtype access domain range
    -> domain
    -> (Maybe range -> t)
    -> M' t
  MAssign
    :: (
       )
    => PartialFunction mtype ReadWrite domain range
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

at :: PartialFunction mtype access domain range -> domain -> M (Maybe range)
at pf x = liftF (MAt pf x id)

-- | Convenient for feeding results of `at`s to other `at`s; no need to
--   pattern match on the Maybe; we do it for you.
at_ :: PartialFunction mtype access domain range -> Maybe domain -> M (Maybe range)
at_ pf x = case x of
  Just x' -> at pf x'
  Nothing -> return Nothing

assign :: PartialFunction mtype ReadWrite domain range -> domain -> Maybe range -> M ()
assign pf x y = liftF (MAssign pf x y ())

infixr 1 .:=

(.:=) (pf, x) y = assign pf x y

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

data SQLiteManifest :: MType -> Access -> * -> * -> * where
  SQLiteManifest :: SQLiteDescriptor -> BS.ByteString -> SQLiteManifest mtype access domain range

class TextSerializable a where
  textSerialize :: a -> T.Text
  textDeserialize :: T.Text -> Maybe a

instance TextSerializable [Char] where
  textSerialize = T.pack
  textDeserialize = Just . T.unpack

instance TextSerializable Bool where
  textSerialize b = case b of
    True -> "True"
    False -> "False"
  textDeserialize text = case T.unpack text of
    "True" -> Just True
    "False" -> Just False
    _ -> Nothing

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
    let queryString = fromString . B8.unpack $ BS.concat ["SELECT \"2\" FROM ", tableName, " WHERE \"1\"=?"]
    -- ^ SQLite simple doesn't allow query substitution for table name and
    --   where clause simultaneously :(
    y <- query conn queryString (Only key) :: IO [Only T.Text]
    return $ case y of
      [] -> Nothing
      (y' : _) -> Just (fromOnly y')

instance ManifestWrite SQLiteManifest where
  mrangeDump _ = textSerialize
  mset (SQLiteManifest _ tableName) conn key value = case value of
    Nothing -> do
        let queryString = fromString . B8.unpack $ BS.concat ["DELETE FROM ", tableName, " WHERE \"1\"=?"]
        execute conn queryString (Only key)
    Just value -> do
        let list = ["INSERT OR REPLACE INTO ", tableName, " VALUES (?, ?)"]
        let queryString = fromString . B8.unpack . BS.concat $ list
        execute conn queryString (key, value)

pm1 :: PureManifest MNotInjective ReadOnly Bool String
pm1 = pureFunction (\x -> Just $ if x then "foo" else "bar")

pm2 :: PureManifest MInjective ReadOnly Int Int
pm2 = pureInjection (\x -> Just $ x + 1) (\x -> Just $ x - 1)

sq1 :: SQLiteManifest MNotInjective ReadWrite String String
sq1 = SQLiteManifest (SQLD "./test1.db") "test"

sq2 :: SQLiteManifest MNotInjective ReadWrite String Bool
sq2 = SQLiteManifest (SQLD "./test2.db") "test"

pf1 = function pm1

pf0 = injection pm2

pf2 = function sq1

pf3 = function sq2

exampleTerm1 :: M (Maybe String)
exampleTerm1 = do
  foo <- pf1 `at` True
  bar <- pf2 `at` "foo"
  (pf2, "foo") .:= ((++) "!") <$> bar
  return $ (++) <$> foo <*> bar

exampleTerm2 :: M (Maybe String)
exampleTerm2 = (pf1 ~> pf2) `at` True

exampleTerm3 = do
  (pf2, "userA") .:= Just "user@name.com"
  (pf3, "user@name.com") .:= Just False
  (pf2 ~> pf3) `at` "userA"

exampleTerm4 point = do
  x <- pf0 `at` point
  y <- (invert pf0) `at_` x
  return $ (== point) <$> y
