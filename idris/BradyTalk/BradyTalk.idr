

-- https://youtube.com/playlist?list=PLZxlmw4K3ICJw6FAml2yw95B0I--iKQZ_

data MyNat = MyZ | MyS MyNat

data MyList : Type -> Type where
    MyNil : MyList a
    Pend : a -> MyList a -> MyList a

NatList : MyList Nat
NatList = Pend 7 (Pend 5 MyNil)

getLeftElement : (MyList Nat) -> Nat
getLeftElement MyNil = 0
getLeftElement (Pend x _) = x 

example7 : Nat
example7 = getLeftElement NatList



powerTwo : Nat -> Nat
powerTwo Z = 1
powerTwo (S n) = 2 * (powerTwo n)

data Vect : Type -> Nat -> Type where 
    Nil : Vect a 0
    (::) : a -> Vect a k -> Vect a (S k) 
    
parity : Nat -> String
parity Z = "even"
parity (S Z) = "odd"
parity (S (S n)) = parity n

exampleVect0 : Vect String 0
exampleVect0 = Nil
exampleVect1 : Vect String 1
exampleVect1 = "odd" :: Nil

-- pi type

paritySequence : (n : Nat) -> Vect String (n)
paritySequence Z = Nil 
paritySequence (S n) = (parity (S n)) :: (paritySequence n)

-- join (append)

(++) : Vect a m -> Vect a n -> Vect a (m + n)
(++) [] ys = ys 
(++) (x::xs) ys = x :: (xs ++ ys)

-- (paritySequence 3) ++ (paritySequence 2)

total
vAdd : Num a => Vect a n -> Vect a n -> Vect a n
vAdd [] [] = []
vAdd (x::xs) (y::ys) = x + y :: vAdd xs ys

--vAdd [1,2,3] [1,2,3]