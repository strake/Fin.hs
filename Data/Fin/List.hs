module Data.Fin.List (Peano, List (..),
                      fromList, uncons, head, tail, init, last, reverse, rotate, at, swap, (!!), findIndex) where

import Prelude ()
import Data.Bool (Bool, bool)
import Control.Applicative
import Control.Category (id)
import Data.Fin.Private as Fin
import Data.Peano (Peano)

findIndex :: Alternative p => (a -> Bool) -> List n a -> p (Fin n)
findIndex p = \ case
    Nil -> empty
    a:.as -> bool id (pure Zero <|>) (p a) (Succ <$> findIndex p as)
