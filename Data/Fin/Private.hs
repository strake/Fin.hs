{-# LANGUAGE TypeApplications #-}

module Data.Fin.Private where

import Prelude (Functor (..), Show (..), Num (..), Enum (..), Bounded (..), Integral (..), Bool (..), Integer, ($), (&&), fst, snd, flip, uncurry, error)
import Control.Applicative
import Control.Arrow (Kleisli (..))
import Control.Category
import Control.Monad (Monad (..))
import Data.Ap
import Data.Eq
import Data.Foldable
import Data.Foldable1
import Data.Function (on)
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Kind (Type)
import qualified Data.List as L
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe
import Data.Monoid (Monoid (..))
import Data.Natural.Class
import Data.Ord
import Data.Peano (Peano)
import qualified Data.Peano as P
import Data.Semigroup (Semigroup (..))
import Data.Traversable
import Data.Typeable
import qualified Numeric.Natural as N
import Text.Read (Read (..))

data Fin :: Peano -> Type where
    Zero :: Fin (P.Succ n)
    Succ :: Fin n -> Fin (P.Succ n)

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

instance Show (Fin n) where show = show . fromFin @N.Natural

instance Read (Fin P.Zero) where readPrec = empty
instance (Natural n, Read (Fin n)) => Read (Fin (P.Succ n)) where
    readPrec = toFinMay <$> readPrec @N.Natural >>= maybe empty pure

instance Natural n => Bounded (Fin (P.Succ n)) where
    minBound = Zero
    maxBound = getCompose $ natural (Compose Zero) (Compose maxBound)

instance Natural n => Enum (Fin n) where
    toEnum n = natural (error "toEnum @(Fin Zero)") $ case n of
        0 -> Zero
        _ -> Succ (toEnum (pred n))
    fromEnum = unFlip . getCompose $ natural (Compose . Flip $ \ case) $ Compose . Flip $ \ case
        Zero -> 0
        Succ n -> succ (fromEnum n)
    succ = unJoin . getCompose $ natural (Compose . Join $ \ case) $ Compose . Join $ \ case
        Zero -> toEnum 1
        Succ n -> Succ (succ n)
    pred = unJoin . getCompose $ natural (Compose . Join $ \ case) $ Compose . Join $ \ case
        Zero -> error "pred 0"
        Succ n -> inj₁ n
    enumFrom = runKleisli . unJoin . getCompose $ natural (Compose . Join . Kleisli $ \ case) $ Compose . Join . Kleisli @[] $ \ case
        Zero -> Zero : (Succ <$> toList enum)
        Succ n -> (L.tail . enumFrom . inj₁) n

newtype Join s a = Join { unJoin :: s a a }

enum :: Natural n => List n (Fin n)
enum = ap $ natural (Ap Nil) (Ap (Zero :. (Succ <$> enum)))

instance Natural n => Num (Fin n) where
    (+) = unJoin₂ . getCompose $ natural (Compose . Join₂ $ \ case) $ Compose . Join₂ $ \ a b -> toFin $ ((+) @N.Natural `on` fromFin) a b
    (-) = unJoin₂ . getCompose $ natural (Compose . Join₂ $ \ case) $ Compose . Join₂ $ \ a b -> toFin $ ((-) @  Integer `on` fromFin) a b
    (*) = unJoin₂ . getCompose $ natural (Compose . Join₂ $ \ case) $ Compose . Join₂ $ \ a b -> toFin $ ((*) @N.Natural `on` fromFin) a b
    abs = id
    negate = unJoin . getCompose $ natural (Compose . Join $ \ case) $ Compose . Join $ \ a -> toFin $ (negate @Integer . fromFin) a
    signum = unJoin . getCompose $ natural (Compose . Join $ \ case) $ Compose . Join $ \ case
        Zero -> Zero
        Succ _ -> toFin (1 :: N.Natural)
    fromInteger n = natural (error "fromInteger @(Fin Zero)") (toFin n)

newtype Join₂ s a = Join₂ { unJoin₂ :: s a (s a a) }

inj₁ :: Fin n -> Fin (P.Succ n)
inj₁ Zero = Zero
inj₁ (Succ n) = Succ (inj₁ n)

proj₁ :: Natural n => Fin (P.Succ n) -> Maybe (Fin n)
proj₁ = unProj₁ $ natural (Proj₁ $ \ case Zero -> Nothing
                                          Succ n -> case n of)
                          (Proj₁ $ \ case Zero -> Just Zero
                                          Succ n -> Succ <$> proj₁ n)

newtype Proj₁ n = Proj₁ { unProj₁ :: Fin (P.Succ n) -> Maybe (Fin n) }

lift₁ :: (Fin m -> Fin n) -> Fin (P.Succ m) -> Fin (P.Succ n)
lift₁ _ Zero = Zero
lift₁ f (Succ n) = Succ (f n)

fromFin :: Integral a => Fin n -> a
fromFin Zero = 0
fromFin (Succ n) = succ (fromFin n)

toFin :: ∀ n a . (Natural n, Integral a) => a -> Fin (P.Succ n)
toFin = fromJust . toFinMay . (`mod` getConst (iterate @n (+1) 1))

toFinMay :: (Natural n, Integral a) => a -> Maybe (Fin n)
toFinMay = getCompose . getCompose $
           natural (Compose . Compose $ pure Nothing)
                   (Compose . Compose $ \ case 0 -> Just Zero
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

newtype T a n = T { t :: [a] -> Maybe (List n a) }

instance Semigroup a => Semigroup (List n a) where
    Nil <> Nil = Nil
    (x:.xs) <> (y:.ys) = x<>y:.xs<>ys

instance (Natural n, Monoid a) => Monoid (List n a) where
    mempty = unFlip $ natural (Flip Nil) (Flip $ mempty:.mempty)
    mappend = (<>)

instance Natural n => Applicative (List n) where
    pure a = unFlip $ natural (Flip Nil) (Flip $ a:.pure a)
    (<*>) = unS $ natural (S $ \ Nil Nil -> Nil)
                          (S $ \ (f:.fs) (x:.xs) -> f x :. (fs <*> xs))

newtype Flip f a b = Flip { unFlip :: f b a }

newtype S a b n = S { unS :: List n (a -> b) -> List n a -> List n b }

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

instance Natural n => Foldable1 (List (P.Succ n)) where
    toNonEmpty (a:.as) = a:|toList as

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

rotate :: Fin n -> List n a -> List n a
rotate Zero as = as
rotate (Succ n) as = rotate (inj₁ n) $ last as :. init as

(!!) :: List n a -> Fin n -> a
Nil !! n = case n of
(x:._)  !! Zero = x
(_:.xs) !! Succ n = xs !! n

at :: Functor f => Fin n -> (a -> f a) -> List n a -> f (List n a)
at Zero f (a:.as) = (:.as) <$> f a
at (Succ n) f (a:.as) = (a:.) <$> at n f as

swap :: Fin n -> Fin n -> List n a -> List n a
swap Zero Zero as = as
swap (Succ m) (Succ n) (a:.as) = a:.swap m n as
swap Zero (Succ n) (a:.as) = uncurry (:.) $ at n (flip (,) a) as
swap (Succ m) Zero (a:.as) = uncurry (:.) $ at m (flip (,) a) as
