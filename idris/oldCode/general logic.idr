-- thinning

-- other local set theory ideas

-- 3^2 = 9

square_it : Int -> Int
square_it = \x => x*x

my_theorem : 9 = square_it 3
my_theorem = Refl
--

-- data And a b = And_intro a b
data And : Type -> Type -> Type where
    And_intro : a -> b -> And a b
And_first_projection : And a b -> a
And_first_projection (And_intro a_val b_val) = a_val
And_second_projection : And a b -> b
And_second_projection (And_intro a_val b_val) = b_val
myBoolAndNat : And Bool Nat
myBoolAndNat = And_intro True 7
andTest : Nat
andTest = And_second_projection myBoolAndNat

-- modus ponens
-- ((A implies B) and A) implies B

modus_ponens_witness : (And (a -> b) a) -> b
--modus_ponens_witness = \my_pair => ((And_first_projection my_pair) (And_second_projection my_pair))
modus_ponens_witness (And_intro f a_val) = f a_val


-- modus tollens
-- ((A implies B) and (not B)) implies (not A)
-- is this true in all toposes ?

modus_tollens_witness : (And (a -> b) (b -> Void)) -> (a -> Void)
--modus_tollens_witness = \my_pair => (\a_val => (And_second_projection my_pair) ((And_first_projection my_pair) a_val))
modus_tollens_witness (And_intro f g_bad) = (\a_val => g_bad (f a_val))
--data myNat = Zero | Suc myNat

data MyNat : Type where
    Zero : MyNat
    Suc :  MyNat ->  MyNat



-- the dependent function type 
-- Pi_{x: A} B(x) where B : A -> Type, is written as
-- (x: A) -> B(x)


-- make list of n natural numbers
data MyVect : (n : Nat) -> Type where
    EmptyB : MyVect 0
    ConsB : (x : Nat) -> (xs : MyVect len) -> MyVect (S len)
-- the above is a dependent function sending each natural number to a type
-- Here EmptyB constructs a value of type MyVect 0
-- also, ConsB takes a value x : Nat and a value xs : MyVect len, 
-- and forms a value MyVect (S len)
--
xx : MyVect 3
xx = ConsB 8 (ConsB 5 (ConsB 3 EmptyB))

-- Here is a simple example of a dependent function
-- maps n to a vector of n ones
fullOfOnes : (n: Nat) -> MyVect n
fullOfOnes Z = EmptyB
fullOfOnes (S x) = ConsB 1 (fullOfOnes x)

-- now we will use dependent functions for a proof

plus1 :  MyNat ->  MyNat
plus1 x = Suc x

plus2 :  MyNat ->  MyNat
plus2 x = Suc (Suc x)

--Pi corresponds to forall, so here is proof that forall natural numbers n, we have plus1 (plus1 n) == plus2 n
my_forall_proof : (n: MyNat) -> ((plus2 n) = (plus1 (plus1 n)))
-- so we want to map each natural number to the appropriate identity type
my_forall_proof n = Refl


-- the sigma type of dependent pairs is written as 
--(x : A ** B x)

-- Here is a simple example of dependent pairs
my_example_dependent_pair : (n: Nat ** MyVect n)
my_example_dependent_pair = (3 ** ConsB 8 (ConsB 5 (ConsB 3 EmptyB)))

-- sigma corresponds to "there exists"
-- so here is a proof that there exits n such that plus1 (plus1 n) == plus2 n

my_exists_proof : (n: MyNat ** ((plus2 n) = (plus1 (plus1 n))))
my_exists_proof = (Suc (Suc (Suc Zero)) ** Refl)

-- the dependent pair (3,Refl_(5)) belongs to the 
-- sigma type sigma_{n:MyNat} [((plus2 n) = (plus1 (plus1 n)))], where 
    -- ((plus2 n) = (plus1 (plus1 n))) is an identity type
-- and so by producing an inhabittant of this type, we 
-- prove the existence


plus4 :  MyNat ->  MyNat
plus4 x = Suc (Suc (Suc (Suc x)))

--data MyBooleans = Zer | On

data MyBooleans : Type where
    Zer : MyBooleans
    On : MyBooleans
--

total change_boolean : MyBooleans -> MyBooleans
change_boolean Zer = On
change_boolean On = Zer

total mod2 : MyNat -> MyBooleans
mod2 Zero = Zer
mod2 (Suc x) = change_boolean (mod2 x) 

-- next we want to proves, forall natural numbers n, if (mod2 n) == 0 then (mod2 plus4) == 0    
induction_step_witness : (n: MyNat) -> (mod2 n = Zer) -> (mod2 (plus4 n) = Zer)
induction_step_witness n some_eq = rewrite some_eq in Refl
-- see boro1 for description of rewrite

total two_step_update : MyNat -> MyNat
two_step_update Zero = (Suc Zero)
two_step_update x = Zero
--

total new_mod2 : MyNat -> MyNat
new_mod2 Zero = Zero
new_mod2 (Suc x) = two_step_update x

total four_step_update : MyNat -> MyNat
four_step_update Zero = (Suc Zero)
four_step_update (Suc Zero) = Suc (Suc Zero)
four_step_update (Suc (Suc Zero)) = Suc (Suc (Suc Zero))
four_step_update x = Zero
--

total new_mod4 : MyNat -> MyNat
new_mod4 Zero = Zero
new_mod4 (Suc x) = four_step_update x

new_induction_step_witness : (n: MyNat) -> (new_mod4 n = Zero) -> (new_mod2 n = Zero)
new_induction_step_witness n some_eq = ?prf


-- use rewrite, and same template as second weekday proof 


-- ex falso quodlibet

-- equivalence

-- prove my prime number theorem

-- now want to show, if m is a multiple of 4 then so is m + 4

times2 : MyNat -> MyNat
times2 Zero = Zero
times2 (Suc x) = Suc (Suc (times2 x)) 



-- under the assumption that [(a and b) implies c], we show that [a implies (b implies c)]
assumed_implication : And a b -> c 
resultant_implication : a -> (b -> c)
resultant_implication a_val = (\b_val => assumed_implication (And_intro a_val b_val))


--data Or a b = Or_introl a | Or_intror b
data Or : Type -> Type -> Type where
    Or_introl : a -> Or a b
    Or_intror : b -> Or a b


firstInjection : a -> Or a b
firstInjection a_val = Or_introl a_val

secondInjection : b -> Or a b
secondInjection b_val = Or_intror b_val

coproductyPairArrow : (a -> c) -> (b -> c) -> ((Or a b) -> c)
coproductyPairArrow f g = k where 
    k (Or_introl a_val) = f a_val 
    k (Or_intror b_val) = g b_val

unbox_value_from_left : Or a b -> a
unbox_value_from_left (Or_introl a) = a 


-- If ((A and C) implies D) and ((B and C) implies D) then ((A or B) and C) implies D
assumed_implication1 : And a c -> d
assumed_implication2 : And b c -> d
new_resultant_implication : (And (Or a b) c) -> d
new_resultant_implication (And_intro (Or_introl a_val) c_val) = assumed_implication1 (And_intro a_val c_val)
new_resultant_implication (And_intro (Or_intror b_val) c_val) = assumed_implication2 (And_intro b_val c_val)

h : Void -> Nat
h = void

-- from false, anthing
ex_falso_quodlibet : Void -> a
ex_falso_quodlibet = void

-- (A and (not A)) implies false
i_am_what_i_am_not : And a (a -> Void) -> Void
i_am_what_i_am_not (And_intro a_val f_val) = f_val a_val

-- If (A or B) and (not A) then B
only_option : And (Or a b) (a -> Void) -> b
only_option (And_intro (Or_introl a_val) f) = void((f a_val))
only_option (And_intro (Or_intror b_val) f) = b_val

the_id : (A : Type) -> (A -> A)
the_id k = (\x => x)



