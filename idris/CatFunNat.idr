-- this code can be obtained by doing 
-- git clone https://github.com/statebox/idris-ct.git
-- git checkout a65822b759

--import Utils

import Syntax.PreorderReasoning

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

--


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
--
functorEq :
      (cat1, cat2 : Category)
   -> (fun1, fun2 : CFunctor cat1 cat2)
   -> ((a : obj cat1) -> (mapObj fun1 a = mapObj fun2 a))
   -> ((a, b : obj cat1) -> (f : mor cat1 a b) -> (mapMor fun1 a b f = mapMor fun2 a b f))
   -> fun1 = fun2
functorEq cat1 cat2 fun1 fun2 prfObj prfMor = really_believe_me ()

idFunctor : (cat : Category) -> CFunctor cat cat
idFunctor cat = MkCFunctor
   id
   (\a, b => id)
   (\a => Refl)
   (\a, b, c, f, g => Refl)

functorComposition :
      (cat1, cat2, cat3 : Category)
   -> CFunctor cat1 cat2
   -> CFunctor cat2 cat3
   -> CFunctor cat1 cat3
functorComposition cat1 cat2 cat3 fun1 fun2 = MkCFunctor
   ((mapObj fun2) . (mapObj fun1))
   (\a, b => (mapMor fun2 (mapObj fun1 a) (mapObj fun1 b)) . (mapMor fun1 a b))
   (\a => trans (cong (preserveId fun1 a)) (preserveId fun2 (mapObj fun1 a)))
   (\a, b, c, f, g => trans (cong (preserveCompose fun1 a b c f g))
                            (preserveCompose fun2
                                             (mapObj fun1 a)
                                             (mapObj fun1 b)
                                             (mapObj fun1 c)
                                             (mapMor fun1 a b f)
                                             (mapMor fun1 b c g)))

--
record NaturalTransformation
   (cat1 : Category)
   (cat2 : Category)
   (fun1 : CFunctor cat1 cat2)
   (fun2 : CFunctor cat1 cat2)
   where
     constructor MkNaturalTransformation
     component : (a : obj cat1) -> mor cat2 (mapObj fun1 a) (mapObj fun2 a)
     commutativity : (a, b : obj cat1)
                  -> (f : mor cat1 a b)
                  -> compose cat2
                             (mapObj fun1 a)
                             (mapObj fun2 a)
                             (mapObj fun2 b)
                             (component a)
                             (mapMor fun2 a b f)
                   = compose cat2
                             (mapObj fun1 a)
                             (mapObj fun1 b)
                             (mapObj fun2 b)
                             (mapMor fun1 a b f)
                             (component b)

naturalTransformationExt :
   (cat1, cat2 : Category)
   -> (fun1, fun2 : CFunctor cat1 cat2)
   -> (trans1, trans2 : NaturalTransformation cat1 cat2 fun1 fun2)
   -> ((a : obj cat1) -> component trans1 a = component trans2 a)
   -> trans1 = trans2
naturalTransformationExt cat1 cat2 fun1 fun2 trans1 trans2 eq = really_believe_me()

naturalTransformationComposition :
   (cat1, cat2 : Category)
   -> (fun1, fun2, fun3 : CFunctor cat1 cat2)
   -> NaturalTransformation cat1 cat2 fun1 fun2
   -> NaturalTransformation cat1 cat2 fun2 fun3
   -> NaturalTransformation cat1 cat2 fun1 fun3
naturalTransformationComposition cat1 cat2 fun1 fun2 fun3
   (MkNaturalTransformation comp1 comm1)
   (MkNaturalTransformation comp2 comm2) =
     MkNaturalTransformation
       (\a => compose cat2 (mapObj fun1 a) (mapObj fun2 a) (mapObj fun3 a) (comp1 a) (comp2 a))
       (\x, y, f =>
         (compose cat2 _ _ _ (compose cat2 _ _ _ (comp1 x) (comp2 x)) (mapMor fun3 _ _ f))
           ={ sym $ (associativity cat2 _ _ _ _ (comp1 x) (comp2 x) (mapMor fun3 x y f)) }=
         (compose cat2 _ _ _ (comp1 x) (compose cat2 _ _ _ (comp2 x) (mapMor fun3 _ _ f)))
           ={ cong $ comm2 x y f }=
         (compose cat2 _ _ _ (comp1 x) (compose cat2 _ _ _ (mapMor fun2 _ _ f) (comp2 y)))
           ={ associativity cat2 _ _ _ _ (comp1 x) (mapMor fun2 x y f) (comp2 y) }=
         (compose cat2 _ _ _ (compose cat2 _ _ _ (comp1 x) (mapMor fun2 _ _ f)) (comp2 y))
           ={ cong {f = \h => compose cat2 _ _ _ h (comp2 y)} $ comm1 x y f }=
         (compose cat2 _ _ _ (compose cat2 _ _ _ (mapMor fun1 x y f) (comp1 y)) (comp2 y))
           ={ sym $ associativity cat2 _ _ _ _ (mapMor fun1 _ _ f) (comp1 y) (comp2 y) }=
         (compose cat2 _ _ _ (mapMor fun1 _ _ f) (compose cat2 _ _ _ (comp1 y) (comp2 y)))
       QED)
--


idTransformation :
   (cat1, cat2 : Category)
   -> (fun : CFunctor cat1 cat2)
   -> NaturalTransformation cat1 cat2 fun fun
idTransformation cat1 cat2 fun = MkNaturalTransformation
   (\a => identity cat2 (mapObj fun a))
   (\a, b, f =>
   (compose cat2 _ _ _ (identity cat2 (mapObj fun a)) (mapMor fun a b f))
   ={ leftIdentity cat2 _ _ (mapMor fun a b f) }=
   (mapMor fun a b f)
   ={ sym $ rightIdentity cat2 _ _ (mapMor fun a b f) }=
   (compose cat2 _ _ _ (mapMor fun a b f) (identity cat2 (mapObj fun b)))
   QED)
--
functorCategory : (cat1, cat2 : Category) -> Category
functorCategory cat1 cat2 = MkCategory
   (CFunctor cat1 cat2)
   (NaturalTransformation cat1 cat2)
   (idTransformation cat1 cat2)
   (naturalTransformationComposition cat1 cat2)
   (\fun1, fun2, (MkNaturalTransformation comp comm) =>
     naturalTransformationExt cat1 cat2 fun1 fun2 _
       (MkNaturalTransformation comp comm)
       (\a => (leftIdentity _ _ _ _)))
   (\fun1, fun2, (MkNaturalTransformation comp comm) =>
     naturalTransformationExt cat1 cat2 fun1 fun2 _
       (MkNaturalTransformation comp comm)
       (\a => (rightIdentity _ _ _ _)))
   (\fun1, fun2, fun3, fun4,
     (MkNaturalTransformation comp1 comm1),
     (MkNaturalTransformation comp2 comm2),
     (MkNaturalTransformation comp3 comm3) =>
       naturalTransformationExt cat1 cat2 fun1 fun4 _ _
       (\a => associativity _ _ _ _ _ _ _ _))
--

catsLeftIdentity :
      (cat1, cat2 : Category)
   -> (func : CFunctor cat1 cat2)
   -> functorComposition cat1 cat1 cat2 (idFunctor cat1) func = func
--
catsLeftIdentity cat1 cat2 func = functorEq
   cat1
   cat2
   (functorComposition cat1 cat1 cat2 (idFunctor cat1) func)
   func
   (\a => Refl)
   (\a, b, f => Refl)
--
catsRightIdentity :
      (cat1, cat2 : Category)
   -> (func : CFunctor cat1 cat2)
   -> functorComposition cat1 cat2 cat2 func (idFunctor cat2) = func
--
catsRightIdentity cat1 cat2 func = functorEq
   cat1
   cat2
   (functorComposition cat1 cat2 cat2 func (idFunctor cat2))
   func
   (\a => Refl)
   (\a, b, f => Refl)
--
catsAssociativity :
      (cat1, cat2, cat3, cat4 : Category)
   -> (func1 : CFunctor cat1 cat2)
   -> (func2 : CFunctor cat2 cat3)
   -> (func3 : CFunctor cat3 cat4)
   -> functorComposition cat1 cat2 cat4 func1 (functorComposition cat2 cat3 cat4 func2 func3)
    = functorComposition cat1 cat3 cat4 (functorComposition cat1 cat2 cat3 func1 func2) func3
--
catsAssociativity cat1 cat2 cat3 cat4 func1 func2 func3 = functorEq
    cat1
    cat4
    (functorComposition cat1 cat2 cat4 func1 (functorComposition cat2 cat3 cat4 func2 func3))
    (functorComposition cat1 cat3 cat4 (functorComposition cat1 cat2 cat3 func1 func2) func3)
    (\a => Refl)
    (\a, b, f => Refl)

--catsAsCategory : Category
--catsAsCategory = MkCategory
--   Category
--   CFunctor
--   idFunctor
--   functorComposition
--   catsLeftIdentity
--   catsRightIdentity
--   catsAssociativity
--

-- uncommenting out the above code, and running, produces "universe inconsistency", 
-- presumably this is a russle style paradox from having a category of categories

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
--myleftIdentity a b f = ?wat
-- :t ?wat 
myleftIdentity a b f = Refl
    
-- :doc Type
-- :printdef modInt
-- :printdef snd


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

------------------------------------ single arrow category

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

singleArrowCategory : Category
singleArrowCategory = MkCategory FunCatObj FunCatMor FunCatId FunCatComp FunCatLeftIdentity FunCatRightIdentity FunCatAssociativity

---- make category of functions

categoryOfFunctions : Category

categoryOfFunctions = functorCategory singleArrowCategory theCategorySet

-----------------------------------------

------------------------------------ parallel arrow category (category11)

--data MyUnit = Star
data Cat11Obj = Eo | Vo
data Arrows11 = Sa | Ta


total
Cat11Mor : Cat11Obj -> Cat11Obj -> Type
Cat11Mor Eo Eo =  MyUnit
Cat11Mor Eo Vo =  Arrows11
Cat11Mor Vo Eo =  Void
Cat11Mor Vo Vo =  MyUnit

Cat11Id : (a : Cat11Obj) -> Cat11Mor a a
Cat11Id Eo = Star
Cat11Id Vo = Star

Cat11Comp       : (a, b, c : Cat11Obj)
                 -> (f : Cat11Mor a b)
                 -> (g : Cat11Mor b c)
                 -> Cat11Mor a c
                 
Cat11Comp Eo Eo Eo Star Star = Star
Cat11Comp Eo Eo Vo Star Sa = Sa
Cat11Comp Eo Eo Vo Star Ta = Ta
Cat11Comp Eo Vo Vo Sa Star = Sa
Cat11Comp Eo Vo Vo Ta Star = Ta
Cat11Comp Vo Vo Vo Star Star = Star

Cat11LeftIdentity  : (a, b : Cat11Obj)
                 -> (f : Cat11Mor a b)
                 -> Cat11Comp a a b (Cat11Id a) f = f
Cat11LeftIdentity Eo Eo Star = Refl
Cat11LeftIdentity Eo Vo Sa = Refl
Cat11LeftIdentity Eo Vo Ta = Refl
Cat11LeftIdentity Vo Vo Star = Refl


Cat11RightIdentity : (a, b : Cat11Obj)
                 -> (f : Cat11Mor a b)
                 -> Cat11Comp a b b f (Cat11Id b) = f
Cat11RightIdentity Eo Eo Star = Refl
Cat11RightIdentity Eo Vo Sa = Refl
Cat11RightIdentity Eo Vo Ta = Refl
Cat11RightIdentity Vo Vo Star = Refl

Cat11Associativity : (a, b, c, d : Cat11Obj)
                 -> (f : Cat11Mor a b)
                 -> (g : Cat11Mor b c)
                 -> (h : Cat11Mor c d)
                 -> Cat11Comp a b d f (Cat11Comp b c d g h) = Cat11Comp a c d (Cat11Comp a b c f g) h
Cat11Associativity Eo Eo Eo Eo Star Star Star = Refl
Cat11Associativity Eo Eo Eo Vo Star Star Sa = Refl
Cat11Associativity Eo Eo Eo Vo Star Star Ta = Refl
Cat11Associativity Eo Eo Vo Vo Star Sa Star = Refl
Cat11Associativity Eo Eo Vo Vo Star Ta Star = Refl
Cat11Associativity Eo Vo Vo Vo Sa Star Star = Refl
Cat11Associativity Eo Vo Vo Vo Ta Star Star = Refl
Cat11Associativity Vo Vo Vo Vo Star Star Star = Refl

category11 : Category
category11 = MkCategory Cat11Obj Cat11Mor Cat11Id Cat11Comp Cat11LeftIdentity Cat11RightIdentity Cat11Associativity

---- make category of functions

categoryOfGraphs : Category

categoryOfGraphs = functorCategory category11 theCategorySet


---------------- do graph example

data Ge = Le | Re
data Gv = Lv | Rv
idGe : Ge -> Ge
idGe = (\em => em)
idGv : Gv -> Gv
idGv = (\x => x)
sourceMap : Ge -> Gv
sourceMap Le = Rv
sourceMap Re = Lv
targetMap : Ge -> Gv
targetMap Le = Lv
targetMap Re = Rv



TwoWayMapObj          : obj Main.category11 -> obj Main.theCategorySet
TwoWayMapObj Eo = Ge
TwoWayMapObj Vo = Gv
TwoWayMapMor          : (a, b : obj Main.category11)
                  -> mor Main.category11 a b
                  -> mor Main.theCategorySet (TwoWayMapObj a) (TwoWayMapObj b)
TwoWayMapMor Eo Eo Star = idGe
TwoWayMapMor Eo Vo Sa = sourceMap
TwoWayMapMor Eo Vo Ta = targetMap
TwoWayMapMor Vo Vo Star = idGv
TwoWayPreserveId      : (a : obj Main.category11)
                  -> TwoWayMapMor a a (identity Main.category11 a) = identity Main.theCategorySet (TwoWayMapObj a)
TwoWayPreserveCompose : (a, b, c : obj Main.category11)
                  -> (f : mor Main.category11 a b)
                  -> (g : mor Main.category11 b c)
                  -> TwoWayMapMor a c (compose Main.category11 a b c f g)
                   = compose Main.theCategorySet (TwoWayMapObj a) (TwoWayMapObj b) (TwoWayMapObj c) (TwoWayMapMor a b f) (TwoWayMapMor b c g)
-- need to fill the holes here

myFirstFunctor : CFunctor Main.category11 Main.theCategorySet
myFirstFunctor = MkCFunctor TwoWayMapObj TwoWayMapMor TwoWayPreserveId TwoWayPreserveCompose

myFirstNat : NaturalTransformation Main.category11 Main.theCategorySet Main.myFirstFunctor Main.myFirstFunctor
myFirstNat = idTransformation Main.category11 Main.theCategorySet Main.myFirstFunctor


-- still have to turn this functor into an oject of the category of graphs, 
-- also have to fill holes, and code a natural transformation, and encode that as an arrow 


-- implement category of dynamical systems
-- fix category of categories
-- encode adjunctions
-- encode Cat <-> Graph adjoint functions
-- encode Kan extensions