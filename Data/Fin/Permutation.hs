{-# LANGUAGE TypeApplications #-}

-- | See 'Permutation'
module Data.Fin.Permutation (Permutation, apply, unapply, swap, orbit, cycles) where

import Prelude (Functor (..), Applicative (..), Eq (..), Show (..), Bool (..), ($), (<$>), otherwise, snd, flip, curry, uncurry)
import Algebra
import Control.Category (Category (..))
import Data.Fin
import Data.Fin.List hiding (swap)
import qualified Data.Fin.List as L
import Data.Foldable (elem, minimum, toList)
import Data.Functor.Compose (Compose (..))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Natural.Class (Natural (..))
import qualified Data.Peano as P
import Data.Universe.Class

-- | Permutation of @n@ elements
--
-- Any permutation can be expressed as a product of transpositions. Ergo, construct with 'Semigroup' operations and `swap`.
data Permutation n where
    PZ :: Permutation P.Zero
    PS :: Fin (P.Succ n) -> Permutation n -> Permutation (P.Succ n)

deriving instance Eq (Permutation n)
deriving instance Show (Permutation n)

instance Natural n => Universe (Permutation n) where
    universe = getCompose $ natural (Compose [PZ]) (Compose $ PS <$> toList enum <*> universe)

instance Natural n => Finite (Permutation n)

apply :: Permutation n -> List n a -> List n a
apply PZ Nil = Nil
apply (PS Zero p) (a:.as) = a:.apply p as
apply (PS (Succ n) p) (a:.as) = uncurry (:.) $ at n (flip (,) a) (apply p as)

unapply :: Permutation n -> List n a -> List n a
unapply PZ Nil = Nil
unapply (PS Zero p) (a:.as) = a:.unapply p as
unapply (PS (Succ n) p) (a:.as) = unapply (PS Zero p) . uncurry (:.) $ at n (flip (,) a) as

instance Natural n => Semigroup (Permutation n) where
    (<>) = unOp₂ $ natural (Op₂ . curry $ \ (PZ, PZ) -> PZ) $ Op₂ . curry $ \ case
        (PS m p, PS Zero q) -> PS m (p <> q)
        (PS m p, PS n q) -> case invert (PS n (invert p)) of
            PS o r -> case (m, o) of
                (Zero, _) -> PS o (r <> q)
                (_, Zero) -> PS m (r <> q)
                (Succ m, Succ o) -> PS (Succ o) (swap m o <> r <> q)

instance Natural n => Monoid (Permutation n) where
    mempty = natural PZ $ PS Zero mempty

instance Natural n => Group (Permutation n) where
    invert = snd . go
      where
        go :: ∀ n . Permutation n -> (List n (Fin n), Permutation n)
        go PZ = (Nil, PZ)
        go (PS n p) = (ms, PS m q)
          where (ns, q) = go p
                ms@(m:._) = L.swap Zero n $ Zero:.(Succ <$> ns)

-- | Transposition of the giventh elements
swap :: Natural n => Fin n -> Fin n -> Permutation n
swap = unOp₂ $ natural (Op₂ $ \ case) $ Op₂ . curry $ \ case
    (Zero, Zero) -> mempty
    (Succ m, Succ n) -> PS Zero (swap m n)
    (Zero, Succ n) -> PS (Succ n) mempty
    (Succ m, Zero) -> PS (Succ m) mempty

newtype Op₂ a b n = Op₂ { unOp₂ :: a n -> a n -> b n }

-- | Orbit of the given index under the given permutation
orbit :: Natural n => Permutation n -> Fin n -> NonEmpty (Fin n)
orbit p n = case (!! n) <$> iterate (apply p) enum of
    a:<as -> a:|takeWhile (/= a) as

-- | All the cycles of the given permutation, which are necessarily disjoint
cycles :: ∀ n . Natural n => Permutation (P.Succ n) -> NonEmpty (NonEmpty (Fin (P.Succ n)))
cycles p = nubOn minimum $ orbit p <$> case enum @(P.Succ n) of n:.ns -> n:|toList ns

infixr 5 :<
data Stream a = a :< Stream a
  deriving (Functor)

iterate :: (a -> a) -> a -> Stream a
iterate f a = a :< (f <$> iterate f a)

takeWhile :: (a -> Bool) -> Stream a -> [a]
takeWhile f (a:<as) | f a = a:takeWhile f as
                    | otherwise = []

nubOn :: Eq b => (a -> b) -> NonEmpty a -> NonEmpty a
nubOn f (a:|as) = a:|go [f a] as
  where go _ [] = []
        go bs (a:as) | b `elem` bs = go bs as
                     | otherwise   = a:go (b:bs) as
          where b = f a
