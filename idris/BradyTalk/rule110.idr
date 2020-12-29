-- code rule 110 for radom number generation
-- do matchbox learning method


data Vect : Type -> Nat -> Type where 
    Nil : Vect a 0
    (::) : a -> Vect a k -> Vect a (S k) 

data TwoStates = Off | On


halfLength : Nat
halfLength = 5

length : Nat 
length = 1 + (2 * halfLength)

safeHead : List a -> a -> a
safeHead [] av = av
safeHead (x::xs) av = x

look : Nat -> (List a) -> a -> a
look n d aDef = safeHead (drop n d) aDef
-- modNat
--look n d defaultVal =  head (drop n d)
--look2 : Nat -> (List Nat) -> Nat
--look2 n d =  head ( 1 :: d)

--init : Vect TwoStates length

--buildNext : List a -> List a -> a -> (a -> a -> a -> a) -> List a 
--buildNext prevState me adef fn =

