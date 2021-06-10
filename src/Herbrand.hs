module Herbrand where



import Data.List
import Data.Ord
import Data.Functor

import Control.Monad

import FirstOrder.Formula
import FirstOrder.Signature
import Alternate

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

fromGTerm :: GTerm -> GenTerm a
fromGTerm (GTerm f args) = Fun f $ map fromGTerm args


toGTerm :: GenTerm a -> GTerm
toGTerm (Fun f args) = GTerm f $ map toGTerm args
toGTerm (Var x) = error "not a ground term"


herbrandUni :: Signature -> [GTerm]
herbrandUni sig = toList $ altUni newSig where
  
  
  cts = constants sig
  sortedSig = sortBy (comparing snd) sig

  newSig =  if null cts then (freshFunName sig, 0) : sortedSig else sortedSig
  

  -- if I would use the list monad, `herbrandUni` would only apply the first 
  -- function to constants and applications of itself, other functions would 
  -- wait forever for application
  altUni :: Signature -> Alternate GTerm
  altUni sig = do
    (funName, funArity) <- Alt sig

    args <- replicateM funArity $ altUni sig

    return $ GTerm funName args







