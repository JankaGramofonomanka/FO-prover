module Alternate where


import Control.Applicative
import Control.Monad


newtype Alternate a = Alt [a] deriving (Eq, Ord, Show, Read)
toList :: Alternate a -> [a]
toList (Alt l) = l

fromList :: [a] -> Alternate a
fromList = Alt

alternate :: [a] -> [a] -> [a]
alternate l [] = l
alternate [] l = l
alternate (x : xs) (y : ys) = x : y : alternate xs ys


instance Monad Alternate where
  return a = Alt [a]

  (Alt []) >>= f = Alt []
  (Alt (x : xs)) >>= f = case f x of
    Alt [] -> Alt xs >>= f
    Alt (y : ys) -> Alt $ y : alternate ys (toList $ Alt xs >>= f)



instance Applicative Alternate where
  pure = return
  (<*>) = ap

instance Functor Alternate where
  fmap f (Alt l) = Alt $ fmap f l






