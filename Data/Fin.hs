-- | Finite totally-ordered sets
module Data.Fin (Fin (..), enum, inj₁, proj₁, lift₁, fromFin, toFin, toFinMay, pred) where

import Prelude ()
import Data.Maybe (Maybe (..))
import Data.Fin.Private
import qualified Data.Peano as P

pred :: Fin (P.Succ n) -> Maybe (Fin n)
pred = \ case
    Zero -> Nothing
    Succ n -> Just n
