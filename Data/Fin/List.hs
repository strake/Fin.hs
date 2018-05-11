module Data.Fin.List (module Data.Peano, List (..),
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
data List n a where
    Nil :: List Zero a
    (:.) :: a -> List n a -> List (Succ n) a

deriving instance (Eq   a) => Eq   (List n a)
deriving instance (Ord  a) => Ord  (List n a)
deriving instance Functor     (List n)
deriving instance Foldable    (List n)
deriving instance Traversable (List n)
deriving instance Typeable List

instance Show a => Show (List n a) where
    showsPrec = showsPrec1

instance (Read a, Natural n) => Read (List n a) where
    readPrec = readPrec1

fromList :: Natural n => [a] -> Maybe (List n a)
fromList = t $ natural (T $ \ case [] -> Just Nil
                                   _  -> Nothing)
                       (T $ \ case [] -> Nothing
                                   x:xs -> (x:.) <$> fromList xs)

data T a n = T { t :: [a] -> Maybe (List n a) }

instance Semigroup a => Semigroup (List n a) where
    Nil <> Nil = Nil
    (x:.xs) <> (y:.ys) = x<>y:.xs<>ys

instance (Semigroup a, Monoid a) => Monoid (List Zero a) where
    mempty = Nil
    mappend = (<>)

instance (Semigroup a, Semigroup (List n a),
          Monoid a, Monoid (List n a)) => Monoid (List (Succ n) a) where
    mempty = mempty:.mempty
    mappend = (<>)

instance Applicative (List Zero) where
    pure _ = Nil
    Nil <*> Nil = Nil

instance (Applicative (List n)) => Applicative (List (Succ n)) where
    pure x = x :. pure x
    f:.fs <*> x:.xs = f x :. (fs <*> xs)

instance Eq1 (List n) where
    liftEq _ Nil Nil = True
    liftEq (==) (x:.xs) (y:.ys) = x == y && liftEq (==) xs ys

instance Ord1 (List n) where
    liftCompare _ Nil Nil = EQ
    liftCompare cmp (x:.xs) (y:.ys) = cmp x y <> liftCompare cmp xs ys

instance Show1 (List n) where
    liftShowsPrec sp sl n = liftShowsPrec sp sl n . toList

instance Natural n => Read1 (List n) where
    liftReadPrec rp rl = fromList <$> liftReadPrec rp rl >>= maybe empty pure

uncons :: List (Succ n) a -> (a, List n a)
uncons (x:.xs) = (x, xs)

head :: List (Succ n) a -> a
head = fst . uncons

tail :: List (Succ n) a -> List n a
tail = snd . uncons

init :: List (Succ n) a -> List n a
init (_:.Nil)       = Nil
init (x:.xs@(_:._)) = x:.init xs

last :: List (Succ n) a -> a
last (x:.Nil) = x
last (_:.xs@(_:._)) = last xs

reverse :: List n a -> List n a
reverse Nil = Nil
reverse xs@(_:._) = liftA2 (:.) last (reverse . init) xs
