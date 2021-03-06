module FirstOrder.Skolemization where

import Data.List
import Control.Monad.State.Strict

import FirstOrder.Formula
import Utils

-- utils ----------------------------------------------------------------------
generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]


renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)


fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = liftM Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi
        
        go2 quantifier x phi = do 
            xs <- get
            let y = head [y | y <- variants x, not $ y `elem` xs]
            let psi = rename x y phi
            put $ y : xs
            liftM (quantifier y) $ go psi



vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = variables (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = not $ x `elem` vars phi


freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]


-- nnf ------------------------------------------------------------------------
nnf :: Formula -> Formula
nnf ?? = case ?? of
  T -> T
  F -> F
  Rel ?? terms -> ??
  
  Not T -> F
  Not F -> T
  Not (Rel ?? terms) -> ??
  Not ?? -> nnf $ pushNegation ??
  
  And ?? ?? -> And (nnf ??) (nnf ??)
  Or ?? ?? -> Or (nnf ??) (nnf ??)
  
  Implies ?? ?? -> nnf $ disassemble ??
  Iff ?? ?? -> nnf $ disassemble ??
  
  Exists x ?? -> Exists x $ nnf ??
  Forall x ?? -> Forall x $ nnf ??

  where
  

  disassemble :: Formula -> Formula
  disassemble ?? = case ?? of
    Implies ?? ?? -> (Not ??) ??? ??
    Iff ?? ?? -> ((Not ??) ??? ??) ??? (?? ??? Not ??)
    _ -> ??

  pushNegation :: Formula -> Formula
  pushNegation (Not ??) = case ?? of
    T -> F
    F -> T
    Rel ?? terms -> Not ??
    
    Not ?? -> ??

    And ?? ?? -> (Not ??) ??? (Not ??)
    Or ?? ?? -> (Not ??) ??? (Not ??)

    Implies ?? ?? -> pushNegation $ Not $ disassemble ??
    Iff ?? ?? -> pushNegation $ Not $ disassemble ??
    
    Exists x ?? -> Forall x (Not ??)
    Forall x ?? -> Exists x (Not ??)

  pushNegation ?? = ??


-- pnf ------------------------------------------------------------------------
pnf :: Formula -> Formula
pnf ?? = nnfToPnf $ nnf ?? where

  nnfToPnf :: Formula -> Formula
  nnfToPnf ?? = case ?? of
      
    And ?? ?? -> pullRight $ pullLeft $ And (nnfToPnf ??) (nnfToPnf ??)
    Or ?? ?? -> pullRight $ pullLeft $ Or (nnfToPnf ??) (nnfToPnf ??)
    
    Exists x ?? -> Exists x $ nnfToPnf ??
    Forall x ?? -> Forall x $ nnfToPnf ??
    
    _ -> ??

  pullLeft :: Formula -> Formula
  pullLeft (?? `And` ??) = pullL And ?? ?? 
  pullLeft (?? `Or` ??) = pullL Or ?? ??
  pullLeft _ = error "bad formula"

  pullL :: (Formula -> Formula -> Formula) -> Formula -> Formula -> Formula
  pullL op ?? ?? = case ?? of
    Exists x ?? -> pullLL Exists x ??
    Forall x ?? -> pullLL Forall x ??
    _ -> op ?? ??
    
    where
      pullLL quantifier x ?? = if freshIn x ?? then 
          quantifier x $ pullLeft (?? `op` ??) 
        else let
            freshX = freshVariant x (?? `op` ??)
          in quantifier freshX $ pullLeft $ (rename x freshX ??) `op` ??


  pullRight :: Formula -> Formula
  pullRight (Exists x ??) = Exists x $ pullRight ??
  pullRight (Forall x ??) = Forall x $ pullRight ??
  pullRight ?? = rev $ pullLeft $ rev ?? where
    rev (?? `And` ??) = (?? `And` ??)
    rev (?? `Or` ??) = (?? `Or` ??)
    rev ?? = ??




-- Skolemization --------------------------------------------------------------
skolemize :: Formula -> Formula
skolemize ?? = pnf $ removeExists $ fresh $ nnf $ generalise ?? where

  removeExists :: Formula -> Formula
  removeExists ?? = evalState (remEx ??) []

  remEx :: Formula -> State [VarName] Formula
  remEx ?? = case ?? of
    T -> return T
    F -> return F
    Rel ?? terms -> return $ Rel ?? terms
    Not ?? -> do
      cleanPhi <- remEx ??
      return $ Not cleanPhi
      
    And ?? ?? -> remExBinary And ?? ??
    Or ?? ?? -> remExBinary Or ?? ??
    Implies ?? ?? -> remExBinary Implies ?? ??
    Iff ?? ?? -> remExBinary Iff ?? ??
    Exists x ?? -> do
      quantifiedVars <- get
      let newX = Fun x $ map Var quantifiedVars
      let substitution = update Var x newX
      let newPhi = apply substitution ??
      newCleanPhi <- remEx newPhi
        
      return $ newCleanPhi
        
    Forall x ?? -> do
      modify (x:)
      cleanPhi <- remEx ??
      return $ Forall x cleanPhi
  
  remExBinary :: (Formula -> Formula -> Formula) -> Formula -> Formula ->
    State [VarName] Formula
  remExBinary op ?? ?? = do
    args <- get
    cleanPhi <- remEx ??
    
    put args
    cleanPsi <- remEx ??
    return $ op cleanPhi cleanPsi
