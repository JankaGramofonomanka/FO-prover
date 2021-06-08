module FirstOrder.Skolemization where

import Data.List
import Control.Monad.State.Strict

import FirstOrder.Formula

-- utils ----------------------------------------------------------------------
update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b x | x == a = b
               | otherwise = f x

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
nnf α = case α of
  T -> T
  F -> F
  Rel ρ terms -> α
  
  Not T -> F
  Not F -> T
  Not (Rel ρ terms) -> α
  Not φ -> nnf $ pushNegation α
  
  And φ ψ -> And (nnf φ) (nnf ψ)
  Or φ ψ -> Or (nnf φ) (nnf ψ)
  
  Implies φ ψ -> nnf $ disassemble α
  Iff φ ψ -> nnf $ disassemble α
  
  Exists x φ -> Exists x $ nnf φ
  Forall x φ -> Forall x $ nnf φ

  where
  

  disassemble :: Formula -> Formula
  disassemble α = case α of
    Implies φ ψ -> (Not φ) ∨ ψ
    Iff φ ψ -> ((Not φ) ∨ ψ) ∧ (φ ∨ Not ψ)
    _ -> α

  pushNegation :: Formula -> Formula
  pushNegation (Not α) = case α of
    T -> F
    F -> T
    Rel ρ terms -> Not α
    
    Not φ -> φ

    And φ ψ -> (Not φ) ∨ (Not ψ)
    Or φ ψ -> (Not φ) ∧ (Not ψ)

    Implies φ ψ -> pushNegation $ Not $ disassemble α
    Iff φ ψ -> pushNegation $ Not $ disassemble α
    
    Exists x φ -> Forall x (Not φ)
    Forall x φ -> Exists x (Not φ)

  pushNegation α = α


-- pnf ------------------------------------------------------------------------
pnf :: Formula -> Formula
pnf α = nnfToPnf $ nnf α where

  nnfToPnf :: Formula -> Formula
  nnfToPnf α = case α of
      
    And φ ψ -> pullRight $ pullLeft $ And (nnfToPnf φ) (nnfToPnf ψ)
    Or φ ψ -> pullRight $ pullLeft $ Or (nnfToPnf φ) (nnfToPnf ψ)
    
    Exists x φ -> Exists x $ nnfToPnf φ
    Forall x φ -> Forall x $ nnfToPnf φ
    
    _ -> α

  pullLeft :: Formula -> Formula
  pullLeft (φ `And` ψ) = pullL And φ ψ 
  pullLeft (φ `Or` ψ) = pullL Or φ ψ
  pullLeft _ = error "bad formula"

  pullL :: (Formula -> Formula -> Formula) -> Formula -> Formula -> Formula
  pullL op φ ψ = case φ of
    Exists x β -> pullLL Exists x β
    Forall x β -> pullLL Forall x β
    _ -> op φ ψ
    
    where
      pullLL quantifier x α = if freshIn x ψ then 
          quantifier x $ pullLeft (α `op` ψ) 
        else let
            freshX = freshVariant x (α `op` ψ)
          in quantifier freshX $ pullLeft $ (rename x freshX α) `op` ψ


  pullRight :: Formula -> Formula
  pullRight (Exists x α) = Exists x $ pullRight α
  pullRight (Forall x α) = Forall x $ pullRight α
  pullRight α = rev $ pullLeft $ rev α where
    rev (φ `And` ψ) = (ψ `And` φ)
    rev (φ `Or` ψ) = (ψ `Or` φ)
    rev γ = γ




-- Skolemization --------------------------------------------------------------
skolemize :: Formula -> Formula
skolemize α = pnf $ removeExists $ fresh $ nnf $ generalise α where

  removeExists :: Formula -> Formula
  removeExists α = evalState (remEx α) []

  remEx :: Formula -> State [VarName] Formula
  remEx α = case α of
    T -> return T
    F -> return F
    Rel ρ terms -> return $ Rel ρ terms
    Not φ -> do
      cleanPhi <- remEx φ
      return $ Not cleanPhi
      
    And φ ψ -> remExBinary And φ ψ
    Or φ ψ -> remExBinary Or φ ψ
    Implies φ ψ -> remExBinary Implies φ ψ
    Iff φ ψ -> remExBinary Iff φ ψ
    Exists x φ -> do
      quantifiedVars <- get
      let newX = Fun x $ map Var quantifiedVars
      let substitution = update Var x newX
      let newPhi = apply substitution φ
      newCleanPhi <- remEx newPhi
        
      return $ newCleanPhi
        
    Forall x φ -> do
      modify (x:)
      cleanPhi <- remEx φ
      return $ Forall x cleanPhi
  
  remExBinary :: (Formula -> Formula -> Formula) -> Formula -> Formula ->
    State [VarName] Formula
  remExBinary op φ ψ = do
    args <- get
    cleanPhi <- remEx φ
    
    put args
    cleanPsi <- remEx ψ
    return $ op cleanPhi cleanPsi
