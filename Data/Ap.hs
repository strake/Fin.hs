module Data.Ap where

data Ap f x a = Ap { ap :: f a (x a) }
