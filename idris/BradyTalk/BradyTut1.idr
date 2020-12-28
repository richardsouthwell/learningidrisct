module Basic2

-- apply a vector of fns to a vector of args


data Vect : Type -> Nat -> Type where 
    Nil : Vect a 0
    (::) : a -> Vect a k -> Vect a (S k) 


vApp : Vect (a -> b) n -> Vect a n -> Vect b n

-- actually this code has implicit arguments
-- vApp : {a : Type} -> {b : Type} -> {n : Nat} ->  Vect (a -> b) n -> Vect a n -> Vect b n


vApp Nil Nil = Nil
vApp (fv::fs) (av::as) = (fv av) :: (vApp fs as)

myexfun : Nat -> Nat
myexfun x = 2 * x
myexap : Vect Nat 2
myexap = vApp [myexfun, myexfun] [9, 9]

-- making the inputs explicit .. 

-- vApp : {a : Type} -> {b : Type} -> {n : Nat} ->  Vect (a -> b) n -> Vect a n -> Vect b n

vApp2 : {a : Type} -> {b : Type} -> {n : Nat} ->  Vect (a -> b) n -> Vect a n -> Vect b n
vApp2 Nil Nil = Nil

--vApp2 Nil Nil = ?foo
-- :e
-- :m
-- :t foo


vApp2 (fv::fs) (av::as) = (fv av) :: (vApp2 fs as)

myexfun2 : Nat -> Nat
myexfun2 x = 2 * x
myexap2 : Vect Nat 2
myexap2 = vApp2 {a = Nat} {b = Nat} {n = 2} [myexfun2, myexfun2] [9, 9]