module Herbrand where



import Data.List
import Data.Ord
import Data.Functor

import Control.Applicative
import Control.Monad

import FirstOrder.Formula
import FirstOrder.Signature

data GTerm = GTerm FunName [GTerm] 
  --deriving (Eq, Ord, Show, Read)
  deriving (Eq, Ord, Read)


instance Show GTerm where
  show (GTerm f l) = case l of
    [] -> f
    (t : ts) -> f ++ "(" ++ prtList (t : ts) ++ ")" 
    
    where
      prtList [] = ""
      prtList [x] = show x
      prtList (x : xs) = show x ++ ", " ++ prtList xs



constant :: FunName -> GTerm
constant f = GTerm f []

herbrandUni :: Signature -> [GTerm]
herbrandUni sig = toList $ altUni newSig where
  
  
  cts = constants sig
  sortedSig = sortBy (comparing snd) sig

  newSig =  if null cts then (freshFunName sig, 0) : sortedSig else sortedSig
  

  altUni :: Signature -> Alternate GTerm
  altUni sig = do
    (funName, funArity) <- Alt sig

    args <- replicateM funArity $ altUni sig

    return $ GTerm funName args





-- if I would use the list monad, `herbrandUni` would only apply the first 
-- function to constants and applications of itself, other functions would wait
-- forever for application
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

