add_1 : Nat -> Nat
add_1 x = x + 1

add_2 : Nat -> Nat
add_2 x = x + 2

number_1 : Nat
number_1 = 1

is_it_zero : Nat -> Bool
is_it_zero Z = True
is_it_zero x = False

somethingTrue : Bool
somethingTrue = ((is_it_zero Z) == is_it_zero 0)

my_identity : Nat -> Nat
my_identity x = x

five_if_zero : Nat -> Nat
five_if_zero Z = 5
five_if_zero x = x

data A a b = A_inst a b 

-- A_inst is a function that takes in an input of type a, and an input of type b, and returns 
-- an output of the product type, with a type description that has prefix A 

myBoolAndNat : A Bool Nat
myBoolAndNat = A_inst True 7

myBoolAndNatSecondProjection : A Bool Nat -> Nat
myBoolAndNatSecondProjection (A_inst b n) = n

lucky : Nat
lucky = myBoolAndNatSecondProjection myBoolAndNat

-- note idris can print
-- A_inst Z True

firstProjection : A a b -> a
firstProjection (A_inst a_val b_val) = a_val

productyPair : (c -> a) -> (c -> b) -> (c -> (A a b))
productyPair f g = k where
    k x = A_inst (f x) (g x)

-- A second way is to define products is using `Generalized Algebraic Data Types' syntax is
data A2 : Type -> Type -> Type where 
    A2_inst : a -> b -> A2 a b
-- because A2 makes a type from two types

-- try
-- A2_inst Z True

-- A third, equivalent, definition, is 

data A3 : Type -> Type -> Type
postulate A3_inst : a -> b -> A3 a b

-- here we define an empty data structure, and an axiom for the value constructor 
-- axioms are functions satisfying types, without full construction arguments

-- :t A3
-- :t A_inst

-- fst (3, 4)
-- snd (4, 5)

-- for sum type

data B a b = B_inst_left a | B_inst_right b

-- or equivalently

data B2 : Type -> Type -> Type where
    B2_inst_left : a -> B2 a b
    B2_inst_right : b -> B2 a b

-- :t B
-- :t B_inst_right

firstInjection : a -> B a b
firstInjection a_val = B_inst_left a_val

secondInjection : b -> B a b
secondInjection b_val = B_inst_right b_val

coproductyPairArrow : (a -> c) -> (b -> c) -> ((B a b) -> c)
coproductyPairArrow f g = k where 
    k (B_inst_left a_val) = f a_val 
    k (B_inst_right b_val) = g b_val

unbox_value_from_left : B a b -> a
unbox_value_from_left (B_inst_left a) = a 

-- data Nat = Z | S Nat

-- 1 == 1

-- "Test" : String
-- '!' : Char
-- 1 : Integer
-- [1, 2] : List Integer
-- index 1 [1, 3]
-- https://www.idris-lang.org/docs/current/prelude_doc/docs/Prelude.List.html

-- :doc List

-- a hole is a variable starting with question mark

--test : Bool -> Bool
--test p = ?hole1

-- do :t hole1

-- can use holes for building

-- let ff = 1 in ff

-- in REPL the command below gets us define gg without evaluating it, then one can run gg later
-- :let gg = 1

-- let x = y in e
-- is equivalent to 
-- (\x. e) y

myAdd5 : Nat -> Nat 
myAdd5 = \x => x + 5

myAdder : Nat -> Nat -> Nat
myAdder = \x => (\y => x + y)

addThree : Nat -> Nat -> Nat -> Nat
addThree = (\x, y, z => x + y + z)
my6 : Nat
my6 = addThree 1 2 3
my6b : Nat
my6b = let  addThreeb = (\x, y, z => x + y + z) in addThreeb 1 2 3

my6c : Nat
my6c = let  addThreec = (\x => (\y => (\z => (x + y + z))) ) in addThreec 1 2 3

-- about if 


isItOne : Nat -> String

isItOne x =     (if x == 1 then "yes" else "no")
is42Q : Nat -> Bool
is42Q = (\x => if x == 42 then True else False) 
-- 

-- recursive definition of even
myEven : Nat -> Bool
myEven Z = True
myEven (S k) = not (myEven k)

-- iterative definition of even

myEven2 : Nat -> Bool -> Bool
myEven2 Z t = t
myEven2 (S k) t = myEven2 k (not t)
-- myEven2 8 True


-- recursive definition of factorial
factorial : Nat -> Nat
factorial Z = 1
factorial (S k) = (S k) * (factorial k)

-- iterative definition of factorial
-- factorial with accumulator
fact_iter : Nat -> Nat -> Nat
fact_iter Z acc = acc
fact_iter (S k) acc = fact_iter k (acc * (S k))
factorial2 : Nat -> Nat 
factorial2 n = fact_iter n 1 

isThatAFact : List Nat
isThatAFact = map factorial2 [1..5]

-- try 
-- A3_inst Z True


data MyList a = Cons a (MyList a) | End
-- :t Cons 1 (Cons 2 End)

addLists : MyList a -> MyList a  -> MyList a 
addLists End ys = ys
addLists (Cons x xs) ys = Cons x (addLists xs ys)

-- addLists (Cons 1 (Cons 2 End)) (Cons 1 (Cons 2 End))

-- making a partial function 

myTest : Nat -> String
myTest Z = "Hi"

-- put keyword `total' in front of total functions

total
myTestB : Nat -> String
myTestB Z = "Hi"
myTestB (S k) = "Hello"

myMap : (a -> a) -> List a -> List a
myMap f [] = []
myMap f (x ::xs ) = (f x) :: (myMap f xs)

-- can also define filter and fold

-- make list of n natural numbers
data MyVect : (n : Nat) -> Type where
    EmptyB : MyVect 0
    ConsB : (x : Nat) -> (xs : MyVect len) -> MyVect (S len)
--
xx : MyVect 3
xx = ConsB 8 (ConsB 5 (ConsB 3 EmptyB))

-- MyVect has a natural number n as an input, and a type of a list of n-inegers as an output
-- if n = 0 then the value constructor EmptyB is used to make an empty list
-- otherwise ConsB is used to concatenate  the left entry with a shorter vector

-- get an error by 
--xxx : MyVect 3 
--xxx = ConsB 5 (ConsB 3 EmptyB)

isSingleton : Bool -> Type 
isSingleton False = MyVect 3
isSingleton True = Nat

-- need to work on exc 17

-- implicit parameters

lengthMyVect : MyVect n -> Nat
lengthMyVect {n = k} mylistylist = k
-- curly bracket means we grab k equal to the implcit parameter n used in setting up MyVect
-- lengthMyVect xx

-- we could do the same thing as 
lengthMyVect2 : MyVect n -> Nat
lengthMyVect2 {n = k} _ = k

-- or we could do
lengthMyVect3 : {n : Nat} -> MyVect n -> Nat
lengthMyVect3 {n = k} _ = k

-- use :t to see

-- consider
-- lengthMyVect {n = 1} (ConsB 1 EmptyB)

-- patern matching

data MyListC a = ConsC a (MyListC a) | EndC


total even_members : MyListC Nat -> MyListC Nat
even_members EndC = EndC
even_members (ConsC x xs) = if (myEven x)
                            then (ConsC x (even_members xs))
                            else even_members xs
--

-- interfaces and implementations

-- interfaces are defined with interface keyword

interface Eq2 a where
    areEq : a -> a -> Bool
    notEq : a -> a -> Bool
    --
    notEq x y = not (areEq x y)
    areEq x y = not (notEq x y)
    
    --if == is given then /= can be obtained, or visa versa

--
Eq2 Nat where
    areEq Z Z     = True
    areEq (S x) (S y) = areEq x y


--
data Foo : Type where
    Fooinst : Nat -> String -> Foo
--


--
--
Eq2 Foo where 
    areEq (Fooinst x1 str1) (Fooinst x2 str2) = (x1 == x2) && (str1 == str2)
--
somethingTrue2 : Bool
somethingTrue2 = areEq (Fooinst 7 "god") (Fooinst 7 "god")
-- component wise equality

-- -------------------- proofs


-- Curry-Howard

swap : (a, b) -> (b, a)
swap (a, b) = (b, a)
-- this proves P AND Q implies Q AND P

data And a b = And_intro a b
and_comm : And a b -> And b a
-- this can be thought of as a proof that P AND Q implies Q And P
-- here a is the type of proofs of P, and b is the type of proofs of Q
and_comm (And_intro a b) = And_intro b a 


-- for a type b, saying x : (b = b) is like saying that x is in the diagonal arrow subobject <1_b, 1_b> containedIn b * b

-- or are the members of (a == b) proofs that a = b in Generalized

-- one can prove exists x : alpha by finding an arrow into {x : alpha}

-- :doc (=)

-- the Nat 3

-- :t (5 = 5)

-- data (=) : a -> b -> Type where 
    -- Refl : x = x

-- Refl makes somthing having type (x = x), 
-- as so testing whether Refl is of type (a = b) is like testing 
-- whether a = b, (we are are testing whether a = b is inhabited), 
-- and if it is, then Refl is there (Refl implicitly chooses appropriate x)

data Or a b = Or_introl a | Or_intror b
-- V is the claim a implies (a OR b)
proof_of_V : a -> Or a b
proof_of_V a_val = Or_introl a_val

data Weekday = Mon | Tue | Wed | Thu | Fri | Sat | Sun

total next_day : Weekday -> Weekday
next_day Mon = Tue
next_day Tue = Wed
next_day Wed = Thu
next_day Thu = Fri
next_day Fri = Sat
next_day Sat = Sun
next_day Sun = Mon

our_first_proof : next_day Mon = Tue

-- our first proof is of the type, Tue = Tue, and Refl generates such a type 
-- basically Refl makes a proof that a thing is itself, corresponding to an axiom

our_first_proof = ?prf

our_first_proof2 : next_day Mon = Tue
our_first_proof2 = Refl

--our_first_proof_gone_wrong : next_day Sun = Tue
--our_first_proof_gone_wrong = Refl

is_it_monday : Weekday -> Bool
is_it_monday Mon = True
is_it_monday _ = False

our_second_proof : (day: Weekday) -> day = Mon ->
     is_it_monday day = True
-- logically, this says if we have a Weekday called day, and day is Monday, then it is true that day is Monday
-- type theoretically, our_second_proof is a function, mapping a Weekday called day, 
-- and an entity of type (day = Mon) to an entity of type ((is_it_monday day)=True)

-- the line below fails
--our_second_proof day day_eq_Mon = Refl

our_second_proof day day_eq_Mon = ?prf2

-- doing :t prf2 gives
-- givens
-- day : Main.Weekday
-- day_eq_Mon : (=) day Main.Mon
-------- goal -----
-- prf2 : (=) (Main.is_it_monday day) Prelude.Bool.True

-- one of our givens is that day=Mon
-- that is, we are assuming we have day_eq_Mon : (day=Mon)
-- so we can use rewrite, to substitute the day with Mon in the goal

-- If we have X : x=y then rewrite X in Y replaces x with y in Y

our_second_proof3 : (day: Weekday) -> day = Mon ->
    is_it_monday day = True
our_second_proof3 day day_eq_Mon = rewrite day_eq_Mon in ?prf3
-- :t
--  day : Main.Weekday
--  day_eq_Mon : (=) {A = Main.Weekday} {B = Main.Weekday} day Main.Mon
--  _rewrite_rule : (=) {A = Main.Weekday} {B = Main.Weekday} day Main.Mon
--------------------------------------
--prf3 : (=) {A = Prelude.Bool.Bool} {B = Prelude.Bool.Bool} Prelude.Bool.True Prelude.Bool.True
---
-- our goal is to find a value ?prf3
-- such that the result of evaluating (rewrite day_eq_Mon in ?prf3)
-- is of the appropriate type that the function our_second_proof3 
-- operating on inputs  day : Weekday and day_eq_Mon : (day=Mon)
-- should have.

-- In other words, we want rewrite day_eq_Mon in ?prf3
-- to have the type (is_it_monday day = True)

-- if we can get prf3 to have the type (is_it_monday Mon = True)
-- then by the way rewrite works, it will change this entity into something of type 
-- (is_it_monday day = True)
-- [because rewrite uses our assumed element day_eq_Mon: (day=Mon), to transform something 
-- of type is_it_monday Mon = True to something of the type is_it_monday day = True]

-- however, evaluating is_it_monday Mon, we just get True, so the ?prf3 we want 
-- just has type (True = True), so we can use Refl to generate something of this type.

our_second_proof4 : (day: Weekday) -> day = Mon ->
    is_it_monday day = True
our_second_proof4 day day_eq_Mon = rewrite day_eq_Mon in Refl

-- this type checks, and so gives a proper proof.

-- so basically in this case, 
-- Refl is of type (is_it_monday Mon = True)
-- but doing rewrite turns this into something of the type 
-- (is_it_monday day = True), as required

-- for expression E and k: day = Mon we have 
-- rewrite k in E 
-- interchanges day and Mon 

our_third_proof : is_it_monday Tue = True -> Void
-- we want to show that something of the type (is_it_monday Tue = True)
-- [that is, the type False = True], can be sent to the empty type Void
our_third_proof mon_is_Tue = ?prff

our_third_proofB : is_it_monday Tue = True -> Void
our_third_proofB Refl impossible
-- this syntax tells idris that the syntax of False = True is impossible

add_7 : Nat -> Nat
add_7 x = x + 7

-- defining identity arrow as a dependent function (pi type)

my_id : (A : Type) -> A -> A 
my_id A x = x

--  my_id Int 5