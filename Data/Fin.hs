{-# LANGUAGE TypeApplications #-}

module Data.Fin where

import Prelude hiding (iterate)
import Control.Applicative
import Data.Ap
import Data.Fin.List (List (..))
import Data.Foldable
import Data.Function (on)
import Data.Functor.Compose
import Data.Maybe
import Data.Natural.Class
import Data.Peano (Peano)
import qualified Data.Peano as P
import Data.Semigroup (Endo (..))
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
    enumFrom (Succ n) = (tail . enumFrom . inj₁) n

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
