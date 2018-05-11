{-# LANGUAGE TypeApplications #-}

module Data.Fin.Private where

import Prelude (Functor (..), Show (..), Num (..), Enum (..), Bounded (..), Integral (..), Bool (..), Integer, ($), (&&), fst, snd, error)
import Control.Applicative
import Control.Category
import Control.Monad (Monad (..))
import Data.Ap
import Data.Eq
import Data.Foldable
import Data.Function (on)
import Data.Functor.Classes
import Data.Functor.Compose
import qualified Data.List as L
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Natural.Class
import Data.Ord
import Data.Peano (Peano)
import qualified Data.Peano as P
import Data.Semigroup (Semigroup (..), Endo (..))
import Data.Traversable
import Data.Typeable
import qualified Numeric.Natural as N
import Text.Read (Read (..))

data Fin :: Peano -> * where
    Zero :: Fin (P.Succ n)
    Succ :: Fin n -> Fin (P.Succ n)

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

instance Show (Fin n) where show = show . (fromFin :: Fin n -> N.Natural)

instance Read (Fin P.Zero) where readPrec = empty
instance (Natural n, Read (Fin n)) => Read (Fin (P.Succ n)) where
    readPrec = toFinMay <$> readPrec @N.Natural >>= maybe empty pure

instance Bounded (Fin (P.Succ P.Zero)) where
    minBound = Zero
    maxBound = Zero

instance Bounded (Fin n) => Bounded (Fin (P.Succ n)) where
    minBound = Zero
    maxBound = Succ maxBound

instance Enum (Fin P.Zero) where
    toEnum _ = error "toEnum @(Fin Zero)"
    fromEnum = \ case
    succ = \ case
    pred = \ case

instance (Natural n, Enum (Fin n)) => Enum (Fin (P.Succ n)) where
    toEnum 0 = Zero
    toEnum n = Succ (toEnum (pred n))
    fromEnum Zero = 0
    fromEnum (Succ n) = succ (fromEnum n)
    enumFrom Zero = Zero : (Succ <$> toList enum)
    enumFrom (Succ n) = (L.tail . enumFrom . inj₁) n

enum :: Natural n => List n (Fin n)
enum = ap $ natural (Ap Nil) (Ap (Zero :. (Succ <$> enum)))

instance Num (Fin P.Zero) where
    (+) = \ case
    (*) = \ case
    abs = id
    negate = \ case
    signum = \ case
    fromInteger _ = error "fromInteger @(Fin Zero)"

instance (Natural n, Num (Fin n)) => Num (Fin (P.Succ n)) where
    a + b = toFin $ ((+) @N.Natural `on` fromFin) a b
    a - b = toFin $ ((-) @  Integer `on` fromFin) a b
    a * b = toFin $ ((*) @N.Natural `on` fromFin) a b

    abs = id
    signum = lift₁ . appEndo . getCompose $
             natural @n (Compose . Endo $ \ case) (Compose . Endo $ pure Zero)

    fromInteger = toFin

inj₁ :: Fin n -> Fin (P.Succ n)
inj₁ Zero = Zero
inj₁ (Succ n) = Succ (inj₁ n)

lift₁ :: (Fin m -> Fin n) -> Fin (P.Succ m) -> Fin (P.Succ n)
lift₁ _ Zero = Zero
lift₁ f (Succ n) = Succ (f n)

fromFin :: Integral a => Fin n -> a
fromFin Zero = 0
fromFin (Succ n) = succ (fromFin n)

toFin :: ∀ n a . (Natural n, Integral a) => a -> Fin (P.Succ n)
toFin = fromJust . toFinMay . (`mod` getConst (iterate @n (+1) 1))

toFinMay :: (Natural n, Integral a) => a -> Maybe (Fin (P.Succ n))
toFinMay = getCompose . getCompose . getCompose $
           natural (Compose . Compose . Compose $ \ case 0 -> Just Zero
                                                         _ -> Nothing)
                   (Compose . Compose . Compose $ \ case 0 -> Just Zero
                                                         n -> Succ <$> toFinMay (n-1))

infixr 5 :.
data List n a where
    Nil :: List P.Zero a
    (:.) :: a -> List n a -> List (P.Succ n) a

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

instance (Semigroup a, Monoid a) => Monoid (List P.Zero a) where
    mempty = Nil
    mappend = (<>)

instance (Semigroup a, Semigroup (List n a),
          Monoid a, Monoid (List n a)) => Monoid (List (P.Succ n) a) where
    mempty = mempty:.mempty
    mappend = (<>)

instance Applicative (List P.Zero) where
    pure _ = Nil
    Nil <*> Nil = Nil

instance (Applicative (List n)) => Applicative (List (P.Succ n)) where
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

uncons :: List (P.Succ n) a -> (a, List n a)
uncons (x:.xs) = (x, xs)

head :: List (P.Succ n) a -> a
head = fst . uncons

tail :: List (P.Succ n) a -> List n a
tail = snd . uncons

init :: List (P.Succ n) a -> List n a
init (_:.Nil)       = Nil
init (x:.xs@(_:._)) = x:.init xs

last :: List (P.Succ n) a -> a
last (x:.Nil) = x
last (_:.xs@(_:._)) = last xs

reverse :: List n a -> List n a
reverse Nil = Nil
reverse xs@(_:._) = liftA2 (:.) last (reverse . init) xs

(!!) :: List n a -> Fin n -> a
Nil !! n = case n of
(x:._)  !! Zero = x
(_:.xs) !! Succ n = xs !! n
