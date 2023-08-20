module Main

import Data.Vect
import Data.DPair

data Term : Nat -> Type where
    Lit : Nat -> Term n
    Plus : Term n -> Term n -> Term n
    Mult : Term n -> Term n -> Term n
    LetIn : Term n -> Term (S n) -> Term n
    Var : Fin n -> Term n

data EvalTerm : Vect n Nat -> Term n -> Nat -> Type where
    LitE : EvalTerm env (Lit num) num
    PlusE : EvalTerm env t1 n1 -> EvalTerm env t2 n2 -> EvalTerm env (Plus t1 t2) (n1 + n2)
    MultE : EvalTerm env t1 n1 -> EvalTerm env t2 n2 -> EvalTerm env (Mult t1 t2) (n1 * n2)
    LetInE : EvalTerm env t1 n1 -> EvalTerm (n1 :: env) t2 n2 -> EvalTerm env (LetIn t1 t2) n2
    VarE : EvalTerm env (Var idx) (index idx env)

evalWithEnv : (env : Vect n Nat) -> (term : Term n) -> Subset Nat (EvalTerm env term)
evalWithEnv _ (Lit x) = (Element x LitE)
evalWithEnv env (Plus t1 t2) =
  let (Element r1 et1) = evalWithEnv env t1 in
  let (Element r2 et2) = evalWithEnv env t2 in
  Element (r1 + r2) (PlusE et1 et2)
evalWithEnv env (Mult t1 t2) =
  let (Element r1 et1) = evalWithEnv env t1 in
  let (Element r2 et2) = evalWithEnv env t2 in
  Element (r1 * r2) (MultE et1 et2)
evalWithEnv env (LetIn val body) =
  let (Element valr vale) = evalWithEnv env val in
  let (Element bodyr bodye) = evalWithEnv (valr :: env) body in
  Element bodyr (LetInE vale bodye)
evalWithEnv env (Var idx) = Element (index idx env) VarE

eval : Term 0 -> Nat
eval term = fst $ evalWithEnv [] term

main : IO ()
main = print $ eval $ LetIn (Lit 2) $ LetIn (Lit 2) $ LetIn (Plus (Var 0) (Var 1)) $ Mult (Var 0) (Var 0)