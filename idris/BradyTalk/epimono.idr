data And : Type -> Type -> Type where
    And_intro : a -> b -> And a b
And_first_projection : And a b -> a
And_first_projection (And_intro a_val b_val) = a_val
And_second_projection : And a b -> b
And_second_projection (And_intro a_val b_val) = b_val
ProductyPair : (h -> a) -> (h -> b) -> (h -> And a b)
ProductyPair f g = \hv => And_intro (f hv) (g hv)

data MyBool = My0 | My1 

--kernalPair : (a -> b) -> (And a a) -> Bool
--kernalPair f (And_intro ax ay) = if (f ax == f ay) then True else False

-- sigma form of kernalPair
-- coequalizer

--my_example_dependent_pair : (n: Nat ** MyVect n)
--my_example_dependent_pair = (3 ** ConsB 8 (ConsB 5 (ConsB 3 EmptyB)))

equalizer : (a : Type) -> (b: Type) -> (a -> b) -> (a -> b) -> Type
equalizer a b f g = (av : a ** (f av = g av))
-- how to realize this is a 


-- how to implement coequalizers

-- coequalizers can be implemented after implementing connectivity finders for graphs (matrix powering)
-- matrix multiplication from
-- https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Data/Matrix/Numeric.idr
-- store presheaves directly (code for graphs and dynamical systems)
-- given a graph (cE, cV, s : cE -> cV, t : cE -> cV) 
-- have compMap : cV -> cV and compMap 0 = id 
-- Also, if e = (x,y) :cE is the nth edge, then one obtains compMap (n+1), as being equal to compMap n
-- except that (supposing x < y) we then have compMap (n+1) (y) := x  
-- once this has been done for all edges, compMap (D) has a direct image corresponding to the connected 
-- components of our graph
-- this type of approach will work for finite ordered sets, but it would be good to code them as types.