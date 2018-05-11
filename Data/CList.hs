module Data.CList (module Data.Peano,
                   CList (..),
                   fromList, uncons, head, tail, init, last, reverse) where

import Prelude (Bool (..), Show (..), fst, snd, ($), (&&))

import Control.Applicative
import Control.Category
import Control.Monad
import Data.Eq
import Data.Foldable
import Data.Functor.Classes
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Natural.Class
import Data.Ord
import Data.Peano
import Data.Semigroup
import Data.Traversable
import Data.Typeable
import Text.Read (Read (..))

infixr 5 :.

data CList n a where
    Nil :: CList Zero a
    (:.) :: a -> CList n a -> CList (Succ n) a

deriving instance (Eq   a) => Eq   (CList n a)
deriving instance (Ord  a) => Ord  (CList n a)
deriving instance Functor     (CList n)
deriving instance Foldable    (CList n)
deriving instance Traversable (CList n)
deriving instance Typeable CList

instance Show a => Show (CList n a) where
    showsPrec = showsPrec1

instance (Read a, Natural n) => Read (CList n a) where
    readPrec = readPrec1

fromList :: Natural n => [a] -> Maybe (CList n a)
fromList = t $ natural (T $ \ case [] -> Just Nil
                                   _  -> Nothing)
                       (T $ \ case [] -> Nothing
                                   x:xs -> (x:.) <$> fromList xs)

data T a n = T { t :: [a] -> Maybe (CList n a) }

instance Semigroup a => Semigroup (CList n a) where
    Nil <> Nil = Nil
    (x:.xs) <> (y:.ys) = x<>y:.xs<>ys

instance (Semigroup a, Monoid a) => Monoid (CList Zero a) where
    mempty = Nil
    mappend = (<>)

instance (Semigroup a, Semigroup (CList n a),
          Monoid a, Monoid (CList n a)) => Monoid (CList (Succ n) a) where
    mempty = mempty:.mempty
    mappend = (<>)

instance Applicative (CList Zero) where
    pure _ = Nil
    Nil <*> Nil = Nil

instance (Applicative (CList n)) => Applicative (CList (Succ n)) where
    pure x = x :. pure x
    f:.fs <*> x:.xs = f x :. (fs <*> xs)

instance Eq1 (CList n) where
    liftEq _ Nil Nil = True
    liftEq (==) (x:.xs) (y:.ys) = x == y && liftEq (==) xs ys

instance Ord1 (CList n) where
    liftCompare _ Nil Nil = EQ
    liftCompare cmp (x:.xs) (y:.ys) = cmp x y <> liftCompare cmp xs ys

instance Show1 (CList n) where
    liftShowsPrec sp sl n = liftShowsPrec sp sl n . toList

instance Natural n => Read1 (CList n) where
    liftReadPrec rp rl = fromList <$> liftReadPrec rp rl >>= maybe empty pure

uncons :: CList (Succ n) a -> (a, CList n a)
uncons (x:.xs) = (x, xs)

head :: CList (Succ n) a -> a
head = fst . uncons

tail :: CList (Succ n) a -> CList n a
tail = snd . uncons

init :: CList (Succ n) a -> CList n a
init (_:.Nil)       = Nil
init (x:.xs@(_:._)) = x:.init xs

last :: CList (Succ n) a -> a
last (x:.Nil) = x
last (_:.xs@(_:._)) = last xs

reverse :: CList n a -> CList n a
reverse Nil = Nil
reverse xs@(_:._) = liftA2 (:.) last (reverse . init) xs
