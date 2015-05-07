module STLC
import Data.Fin
import Data.Vect

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy (TyFun A T) = interpTy A -> interpTy T

using (G:Vect n Ty)
  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop  : HasType k G t -> HasType (FS k) (u :: G) t
          
  data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i G t -> Expr G t
    Val : (x : Int) -> Expr G TyInt
    Lam : Expr (a :: G) t -> Expr G (TyFun a t)
    App : Expr G (TyFun a t) -> Expr G a -> Expr G t
    Op  : (interpTy a -> interpTy b -> interpTy c) ->
             Expr G a -> Expr G b -> Expr G c
    If  : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a
    
  data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)
            
  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop    (x :: xs) = x
  lookup (Pop k) (x :: xs) = lookup k xs
  
  interp : Env G -> Expr G t -> interpTy t
  interp env (Var i)     = lookup i env
  interp env (Val x)     = x
  interp env (Lam sc)    = \x => interp (x :: env) sc
  interp env (App f s)   = interp env f (interp env s)
  interp env (Op op x y) = op (interp env x) (interp env y)
  interp env (If x t e)  = if interp env x then interp env t
                                           else interp env e
  
-- Unit Tests
  sub1 : Expr G (TyFun TyInt TyInt)
  sub1 = Lam (Op (-) (Var Stop) (Val 1))
  
  sub2 : Expr G (TyFun TyInt TyInt)
  sub2 = Lam (App sub1 (App sub1 (Var Stop)))
  
  add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))

  fact : Expr G (TyFun TyInt TyInt)
  fact = Lam (If (Op (==) (Var Stop) (Val 0))
               (Val 1)
               (Op (*) (App fact (Op (-) (Var Stop) (Val 1)))
                       (Var Stop)))
  
  fib : Expr G (TyFun TyInt TyInt)
  fib = Lam (If (Op (==) (Var Stop) (Val 0))
                (Val 1)
                (If (Op (==) (Var Stop) (Val 1))
                    (Val 1)
                    (Op (*) (App fib (App sub1 (Var Stop)))
                            (App fib (App sub2 (Var Stop))))))
                            
                                                                   
                       
