module Data.Ap where

newtype Ap f x a = Ap { ap :: f a (x a) }
