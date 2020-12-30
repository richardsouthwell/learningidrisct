
-- code that defines categories, has a function to make discrete categories, and makes an example

-- https://arxiv.org/pdf/1912.06191.pdf

-- https://blog.statebox.org/fun-with-categories-70c64649b8e0
-- https://blog.statebox.org/concrete-categories-af444d5f055e
-- https://github.com/statebox/idris-ct


-- https://github.com/statebox/idris-ct/blob/fbc7f633e0d86bfe5b56a2c4b9db6f780d59106d/idris2/Cats/CatsAsCategory.idr
-- https://github.com/statebox/idris-ct/blob/fbc7f633e0d86bfe5b56a2c4b9db6f780d59106d/idris2/Basic/Adjunction.idr
-- can use this to define exponential objects
-- define category of graphs 
-- https://github.com/statebox/idris-ct/blob/master/src/Basic/Functor.lidr
-- https://github.com/statebox/idris-ct/blob/fbc7f633e0d86bfe5b56a2c4b9db6f780d59106d/idris2/Basic/NaturalTransformation.idr


-- used 
--idris2/Basic/Category.idr
--/Discrete/DiscreteCategory.idr



record Category where
    constructor MkCategory
    obj           : Type
    mor           : obj -> obj -> Type
    identity      : (a : obj) -> mor a a
    compose       : (a, b, c : obj)
                 -> (f : mor a b)
                 -> (g : mor b c)
                 -> mor a c
    leftIdentity  : (a, b : obj)
                 -> (f : mor a b)
                 -> compose a a b (identity a) f = f
    rightIdentity : (a, b : obj)
                 -> (f : mor a b)
                 -> compose a b b f (identity b) = f
    associativity : (a, b, c, d : obj)
                 -> (f : mor a b)
                 -> (g : mor b c)
                 -> (h : mor c d)
                 -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h


---------------------------- make discrete category

DiscreteMorphism : (x, y : a) -> Type
DiscreteMorphism x y = (x = y)



discreteIdentity : (x : a) -> DiscreteMorphism x x
discreteIdentity _ = Refl

discreteCompose : (x, y, z : a) -> DiscreteMorphism x y -> DiscreteMorphism y z -> DiscreteMorphism x z
discreteCompose _ _ _ Refl Refl = Refl

discreteLeftIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x x y (discreteIdentity x) f = f
discreteLeftIdentity _ _ Refl = Refl

discreteRightIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x y y f (discreteIdentity y) = f
discreteRightIdentity _ _ Refl = Refl

discreteAssociativity : (w, x, y, z : a)
                     -> (f : DiscreteMorphism w x)
                     -> (g : DiscreteMorphism x y)
                     -> (h : DiscreteMorphism y z)
                     -> discreteCompose w x z f (discreteCompose x y z g h)
                      = discreteCompose w y z (discreteCompose w x y f g) h
discreteAssociativity _ _ _ _ Refl Refl Refl = Refl

discreteCategory : (a : Type) -> Category
discreteCategory a = MkCategory
  a
  DiscreteMorphism
  discreteIdentity
  discreteCompose
  discreteLeftIdentity
  discreteRightIdentity
  discreteAssociativity

data MyBool = MyTrue | MyFalse 

MyFirstCategory : Category
MyFirstCategory = discreteCategory MyBool

-- obj MyFirstCategory


EndomorphismsOfTrue : Type
EndomorphismsOfTrue = mor MyFirstCategory MyTrue MyTrue

MyFirstArrow : EndomorphismsOfTrue
MyFirstArrow = Refl


--------- play

undefinedFun : String -> Nat
-- undefinedFun "h"

--functionalExtensionality : {a : Type} -> {b : Type} -> {f : a -> b} -> {g : a -> b}  ->
--     ((x : a) -> (f x = g x)) -> (f = g)
functionalExtensionality : (a : Type) -> (b : Type) -> (f : a -> b) -> (g : a -> b)  ->
    ((x : a) -> (f x = g x)) -> (f = g)

veryBigCategory : Category
veryBigCategory = discreteCategory Type

VoidID : Void -> Void 
VoidID = void


---------------------- encode Set

setMor : Type -> Type -> Type
setMor a b = (a -> b)

setId : (a : Type) -> setMor a a
setId a = (\x => x) 

mycompose       : (a, b, c : Type)
                 -> (f : setMor a b)
                 -> (g : setMor b c)
                 -> setMor a c

mycompose a b c f g = (\av => g (f av))
myleftIdentity  : (a, b : Type)
                 -> (f : setMor a b)
                 -> mycompose a a b (setId a) f = f
-- myleftIdentity a b f = ?wat
-- :t ?wat 
myleftIdentity a b f = Refl
    

myrightIdentity : (a, b : Type)
                 -> (f : setMor a b)
                 -> mycompose a b b f (setId b) = f
myrightIdentity a b f = Refl
myassociativity : (a, b, c, d : Type)
                 -> (f : setMor a b)
                 -> (g : setMor b c)
                 -> (h : setMor c d)
                 -> mycompose a b d f (mycompose b c d g h) = mycompose a c d (mycompose a b c f g) h
--myassociativity a b c d f g h = ?huh
myassociativity a b c d f g h = Refl
theCategorySet : Category
theCategorySet = MkCategory Type setMor setId mycompose myleftIdentity myrightIdentity myassociativity

------------------------------------

-- Type : Type 1
-- universe heirachy
-- http://docs.idris-lang.org/en/latest/faq/faq.html

-- reddit.com/r/Idris/comments/fzjhny/how_to_prove_functions_are_equal/
-- It can't be proved in general, unfortunately. What you need is function extensionality:
-- forall f g. (forall x. f x = g x) -> f = g
-- Which is not a theorem in Idris. You can use it as an axiom, however.

---------------------------------

-- encode parallel arrow Category
-- encode functors
-- encode natural transformations
-- encode functor category
-- encode Cat
-- encode exponential objects (use adjunction)

--------------------------------------------------------
-- -- encode category for making the category of functions
-- (the category with a single arrow)

-- data MyBool = MyTrue | MyFalse 
data MyUnit = Star
data FunCatObj = Lobj | Vobj
data MyArrow = Pointer


total
FunCatMor : FunCatObj -> FunCatObj -> Type
FunCatMor Lobj Lobj =  MyUnit
FunCatMor Lobj Vobj =  MyArrow
FunCatMor Vobj Lobj =  Void
FunCatMor Vobj Vobj =  MyUnit

FunCatId : (a : FunCatObj) -> FunCatMor a a
FunCatId Lobj = Star
FunCatId Vobj = Star


FunCatComp       : (a, b, c : FunCatObj)
                 -> (f : FunCatMor a b)
                 -> (g : FunCatMor b c)
                 -> FunCatMor a c
                 
FunCatComp Lobj Lobj Lobj Star Star = Star
FunCatComp Lobj Lobj Vobj Star Pointer = Pointer
FunCatComp Lobj Vobj Vobj Pointer Star = Pointer
FunCatComp Vobj Vobj Vobj Star Star = Star

FunCatLeftIdentity  : (a, b : FunCatObj)
                 -> (f : FunCatMor a b)
                 -> FunCatComp a a b (FunCatId a) f = f
FunCatLeftIdentity Lobj Lobj Star = Refl
FunCatLeftIdentity Lobj Vobj Pointer = Refl
FunCatLeftIdentity Vobj Vobj Star = Refl

FunCatRightIdentity : (a, b : FunCatObj)
                 -> (f : FunCatMor a b)
                 -> FunCatComp a b b f (FunCatId b) = f
FunCatRightIdentity Lobj Lobj Star = Refl
FunCatRightIdentity Lobj Vobj Pointer = Refl
FunCatRightIdentity Vobj Vobj Star = Refl

FunCatAssociativity : (a, b, c, d : FunCatObj)
                 -> (f : FunCatMor a b)
                 -> (g : FunCatMor b c)
                 -> (h : FunCatMor c d)
                 -> FunCatComp a b d f (FunCatComp b c d g h) = FunCatComp a c d (FunCatComp a b c f g) h
FunCatAssociativity Lobj Lobj Lobj Lobj Star Star Star = Refl
FunCatAssociativity Lobj Lobj Lobj Vobj Star Star Pointer = Refl
FunCatAssociativity Lobj Lobj Vobj Vobj Star Pointer Star = Refl
FunCatAssociativity Lobj Vobj Vobj Vobj Pointer Star Star = Refl
FunCatAssociativity Vobj Vobj Vobj Vobj Star Star Star = Refl

--myassociativity a b c d f g h = ?huh

-- How to define a function from And Void A to B ? Use permuation of product order !

--FunCatComp _ _ _ Pointer Star = Pointer
--FunCatComp _ _ _ Star Pointer = Pointer

singleArrowCategory : Category
singleArrowCategory = MkCategory FunCatObj FunCatMor FunCatId FunCatComp FunCatLeftIdentity FunCatRightIdentity FunCatAssociativity

---------------------- functors
-- https://github.com/statebox/idris-ct/blob/master/idris2/Basic/Functor.idr

record CFunctor (cat1 : Category) (cat2 : Category) where
    constructor MkCFunctor
    mapObj          : obj cat1 -> obj cat2
    mapMor          : (a, b : obj cat1)
                   -> mor cat1 a b
                   -> mor cat2 (mapObj a) (mapObj b)
    preserveId      : (a : obj cat1)
                   -> mapMor a a (identity cat1 a) = identity cat2 (mapObj a)
    preserveCompose : (a, b, c : obj cat1)
                   -> (f : mor cat1 a b)
                   -> (g : mor cat1 b c)
                   -> mapMor a c (compose cat1 a b c f g)
                    = compose cat2 (mapObj a) (mapObj b) (mapObj c) (mapMor a b f) (mapMor b c g)
  








