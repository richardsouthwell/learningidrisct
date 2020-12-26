-- 1a identity

my_id : (t : Type) -> (t -> t)
my_id t = (\x => x)

--my_id Nat 7


--my_example_dependent_pair : (n: Nat ** MyVect n)
--my_example_dependent_pair = (3 ** ConsB 8 (ConsB 5 (ConsB 3 EmptyB)))


my_bin_op : (t : Type ** (t -> t -> t))
my_bin_op = (Nat ** \x => \y => x + y)

myp1 : (t : Type ** (t -> t -> t)) -> Type
myp1 (x ** y) = x

--myp2 : (t : Type ** (t -> t -> t)) -> (t -> t -> t)
--myp2 (x ** y) = y

fibb : Int -> Int
fibb 0 = 1
fibb 1 = 1
fibb n = fibb (n-1) + fibb (n-2)


-- https://arxiv.org/pdf/1912.06191.pdf

record Category where
    constructor MkCategory
 obj : Type
 mor : obj -> obj -> Type
 identity : ( a : obj ) -> mor a a
 compose : (a , b , c : obj )
 -> ( f : mor a b )
 -> ( g : mor b c )
 -> mor a c
 leftIdentity : (a , b : obj )
 -> ( f : mor a b )
 -> compose a a b ( identity a ) f = f
 rightIdentity : (a , b : obj )
 -> ( f : mor a b )
 -> compose a b b f ( identity b ) = f
 associativity : (a , b , c , d : obj )
 -> ( f : mor a b )
 -> ( g : mor b c )
 -> ( h : mor c d )
 -> compose a b d f ( compose b c d g h )
  = compose a c d ( compose a b c f g ) h


record Person where
    constructor MkPerson
    firstName, middleName, lastName : String
    height : Int

richard : Person
richard = MkPerson "Richard" "Philip" "Southwell" 2

-- firstName richard

DiscreteMorphism : (x, y : a) -> Type
DiscreteMorphism x y = (x = y)
-- (x = y) has one inhabittant iff x and y are equal

data MyBool = MyTrue | MyFalse 

EndomorphismsOfTrue : Type
EndomorphismsOfTrue = DiscreteMorphism MyTrue MyTrue

MyFirstArrow : EndomorphismsOfTrue
MyFirstArrow = Refl

discreteIdentity : (x : a) -> DiscreteMorphism x x
discreteIdentity _ = Refl

discreteCompose : (x, y, z : a)
               -> (f : DiscreteMorphism x y)
               -> (g : DiscreteMorphism y z)
               -> DiscreteMorphism x z
discreteCompose _ _ _ Refl Refl = Refl

discreteLeftId : (x, y : a)
              -> (f : DiscreteMorphism x y)
              -> discreteCompose x x y (discreteIdentity x) f = f
discreteLeftId _ _ Refl = Refl

discreteRightId : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x y y f (discreteIdentity y) = f
discreteRightId _ _ Refl = Refl

discreteAssociativity : (w, x, y, z : a)
                     -> (f : DiscreteMorphism w x)
                     -> (g : DiscreteMorphism x y)
                     -> (h : DiscreteMorphism y z)
                     -> discreteCompose w x z f (discreteCompose x y z g h)
                      = discreteCompose w y z (discreteCompose w x y f g) h
discreteAssociativity _ _ _ _ Refl Refl Refl = Refl


discreteCategory : (a : Type) -> Category

--discreteCategory a = MkCategory
--  a
--  DiscreteMorphism
--  discreteIdentity
--  discreteCompose
--  discreteLeftId
--  discreteRightId
--  discreteAssociativity





