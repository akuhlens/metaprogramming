module GTLC
import Data.Fin
import Data.Vect
import Data.So

%default total

-- The Representation of types
mutual
  data Ty  = TyDyn | TyInt | TyBool | TyFun Ty Ty
 
mutual
  -- The representation of Dyn values
  data Dyn : Type where
    inj : (t : Ty) -> (x : interpTy t) -> Dyn  
  
  -- Convert Ty to Type in proof land
  data Ty2T : Ty -> Type -> Type where
    d2d : Ty2T TyDyn Dyn
    i2i : Ty2T TyInt Int
    b2b : Ty2T TyBool Bool
    f2f : Ty2T a b -> Ty2T c d -> Ty2T (TyFun a c) (b -> Maybe d)
  
  -- Compute the real type of interpreted Ty values
  total
  interpTy : Ty -> Type
  interpTy TyDyn       = Dyn
  interpTy TyInt       = Int
  interpTy TyBool      = Bool
  interpTy (TyFun A T) = (interpTy A) -> Maybe (interpTy T)

  -- Proof that two Types are consistent
data consistTy : Ty -> Ty -> Type where
  refl  : consistTy a     a
  dynR  : consistTy a     TyDyn
  dynL  : consistTy TyDyn a
  funC  : consistTy a b -> consistTy c d -> consistTy (TyFun a c) (TyFun b d)

data joinTy : Ty -> Ty -> Ty -> Type where
  const : joinTy a     a     a
  right : joinTy TyDyn a     a
  left  : joinTy a     TyDyn a
  under : joinTy a     b     c -> joinTy d e f -> 
            joinTy (TyFun a d) (TyFun b e) (TyFun c f) 
  

-- I am Interested in how this is implemented but it represents a type index
-- that allows variables types to be computed computed while typechecking.
using (G : Vect n Ty)

-- An index for variable types
  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop  : HasType k G t -> HasType (FS k) (u :: G) t

-- The Explicitly Typed Cast Calculus
  data Expr : Vect n Ty -> Ty -> Type where
    Var   : HasType i G t -> Expr G t
    ValI  : (v : Int)  -> Expr G TyInt
    ValB  : (v : Bool) -> Expr G TyBool
    ILam  : Expr (a :: G) t -> Expr G (TyFun a t)
    IApp  : Expr G (TyFun a t) -> Expr G a -> Expr G t
    IOp   : (interpTy a -> interpTy b -> interpTy c) ->
             Expr G a -> Expr G b -> Expr G c
    IIf   : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a
    ICast : Expr G t -> (t : Ty) -> (g : Ty) -> Expr G g   
  
  mkCast : Expr G t1 -> (t1 : Ty) -> (t2 : Ty) -> (p : consistTy t1 t2) -> Expr G t2
  mkCast e s t p = (ICast e s t)
--  mkCast refl s t e = e -- mkCast is really dumb currently

  
-- The source level gradual language
  Val : {auto p : Ty2T ty t} -> t -> Expr G ty
  Val {p= i2i} x = ValI x
  Val {p= b2b} x = ValB x

-- Lam is an unannotated lambda
  Lam : Expr (TyDyn :: G) t -> Expr G (TyFun TyDyn t)
  Lam = ILam
-- LamT is a lambda that accecpts a non dynamic type annotation
  LamT : (t : Ty) -> Expr (t :: G) g -> Expr G (TyFun t g) 
  LamT t = ILam
  
-- If is the "smart" constructor for if terms  
  If : Expr G tt -> Lazy (Expr G tc) -> Lazy (Expr G ta) -> 
        {auto ct : consistTy tt TyBool} -> 
        {auto cc : consistTy tc tr} -> 
        {auto ca : consistTy ta tr} -> 
        Expr G tr
  If {ct=dynL}{cc}{ca} t c a = If {ct=refl}{cc}{ca} (ICast t TyDyn TyBool) c a
  If {ct=refl}{cc=refl}{ca=refl} t c a = IIf t c a
  If {ct=refl}{tc}{ta}{tr} t c a = IIf t (ICast c tc tr) (ICast a ta tr)

-- App is the smart constructor for Application terms
  data AppRule : Ty -> Ty -> Ty -> Type where
   fApp : AppRule (TyFun a b) a     b
   dApp : AppRule TyDyn       TyDyn TyDyn
   
  App :  Expr G tf -> Expr G ta -> {auto ar : AppRule tf ra rr} -> 
     {auto cf : consistTy tf (TyFun ra rr)} -> {auto ca : consistTy ta ra} -> Expr G rr
  App f a {tf} {ra} {rr} {ta} = IApp (ICast f tf (TyFun ra rr)) (ICast a ta ra)
    
--  App f x {r} {c}{ta}{ra} = IApp f (ICast x ta ra)
--  App f x {r} {}{ta} = IApp (ICast f TyDyn (TyFun TyDyn TyDyn))
--(ICast x ta TyDyn)
     
-- Op is the smart constructor for operators 

  Op  : (interpTy oa -> interpTy ob -> interpTy c) -> Expr G aa -> Expr G ab ->
           {auto pa : consistTy aa oa} -> {auto pb : consistTy ab ob} -> Expr G c
  Op p a b {pa} {aa} {oa} {pb} {ab} {ob}  = IOp p (mkCast a aa oa pa) (mkCast b ab ob pb)  


-- The lexical environment of the interpreter
  data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)

-- Lookup of lexical values in the interpreter    
  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop    (x :: xs) = x
  lookup (Pop k) (x :: xs) = lookup k xs

  mutual
-- Cast between types computed in the smart constructors
    rtCast : (t : Ty) -> (g : Ty) -> (x : interpTy t) -> Maybe (interpTy g)
    rtCast TyDyn      TyDyn       x          = return x
    rtCast TyInt      TyInt       x          = return x
    rtCast TyBool     TyBool      x          = return x
    rtCast TyDyn      g           (inj t' x) = rtCast t' g x
    rtCast t'         TyDyn       x          = return (inj t' x)
    rtCast (TyFun a b)(TyFun c d) f          = 
             return (\x => rtCast b d !(f !(rtCast c a x)))
    rtCast _          _         _          = Nothing

  -- The GTLC interpreter    
    interp : Env G -> Expr G ty -> Maybe (interpTy ty) 
    interp env (Var i)         = return (lookup i env)
    interp env (ValI x)        = return x
    interp env (ValB x)        = return x
    interp env (ICast x r1 r2) = ?interpICast --rtCast r1 r2 !(interp env x)
    interp env (ILam b)        = return (\x => interp (x :: env) b)
    interp env (IOp op x y)    = return (op !(interp env x) !(interp env y))
    interp env (IApp f s)      = (!(interp env f) !(interp env s)) 
    interp env (IIf t c a)     = return (if !(interp env t) 
                                         then !(interp env c) 
                                         else !(interp env a))
                                                          
-- unit tests
-- unit tests for consist
a2 : consistTy TyInt TyInt 
a2 = refl
a0 : consistTy TyDyn TyDyn
a0 = refl
a1 : consistTy TyDyn TyBool
a1 = dynL
a3 : consistTy TyInt TyDyn
a3 = dynR
a4 : consistTy (TyFun TyInt TyBool) (TyFun TyInt TyBool)
a4 = refl
a5 : consistTy (TyFun TyInt TyBool) (TyFun TyInt TyBool)
a5 = funC refl refl
a6 : consistTy (TyFun TyDyn TyBool) (TyFun TyInt TyDyn)
a6 = funC dynL dynR
-- unit tests of coersion calculus forms
c0 : Expr [] TyInt
c0 = ValI 1
c1 : Expr [] TyBool
c1 = ValB True

-- unit tests of gradually typed forms 
t0 : Expr [] TyInt
t0 = Val 1
t0' : Expr [] TyBool
t0' = Val True
t1 : Expr [] (TyFun TyDyn TyDyn) 
t1 = Lam (Var Stop)                                    
t2 : Expr [] (TyFun TyInt TyInt)  
t2 = LamT TyInt (Var Stop)
-- unit test on the gradual If smart constructor
t3 : Expr [] TyInt 
t3 = (If (ValB True) (ValI 0) (ValI 1))
t4 : Expr [TyDyn] TyInt
t4 = (If (Var Stop) (ValI 0) (ValI 1))
t5 : Expr [TyDyn] TyInt
t5 = (If (Var Stop) (Var Stop) (ValI 1))
t6 : Expr [TyDyn] TyInt
t6 = (If (Var Stop) (Var Stop) (Var Stop))
t7 : Expr [TyDyn] TyDyn
t7 = (If (Var Stop) (ValI 0) (ValB True))
-- unit tests for the gradual App smart constructor
t8 : Expr [] TyInt
t8 = App (LamT TyInt (Var Stop)) (Val 1)
t9 : Expr [] TyDyn
t9 = App (Lam (Var Stop)) (ValI 1)

{-
fact : Expr [] (TyFun TyDyn TyInt)
fact = (Lam (If (Op (==) (Val 0) (Var Stop))
                (Val 1)
                (Op (*) (Var Stop) (App fact (Op (-) (Var Stop) (Val 1))))))
-}
-- unit tests for the interpreter
--i0 : Maybe Int
--i0 = (interp [] (ValI 1))

--main : IO ()
--main = putStrLn (show i0)
