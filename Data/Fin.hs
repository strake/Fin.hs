module Data.Fin where

import Data.Peano (Peano)
import qualified Data.Peano as P

data Fin :: Peano -> * where
    Zero :: Fin (P.Succ n)
    Succ :: Fin n -> Fin (P.Succ n)
