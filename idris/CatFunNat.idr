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