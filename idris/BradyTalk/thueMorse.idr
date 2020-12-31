-- A -> AB, B -> BA


data And : Type -> Type -> Type where
    And_intro : a -> b -> And a b
And_first_projection : And a b -> a
And_first_projection (And_intro a_val b_val) = a_val
And_second_projection : And a b -> b
And_second_projection (And_intro a_val b_val) = b_val
ProductyPair : (h -> a) -> (h -> b) -> (h -> And a b)
ProductyPair f g = \hv => And_intro (f hv) (g hv)

customMap : (a -> b) -> List a -> List b
customMap f [] = []
customMap f (x :: xs) = (f x) :: (customMap f xs) 

data Symbols = A | B

thueMorseFn : Symbols -> And Symbols Symbols
thueMorseFn A = And_intro A B
thueMorseFn B = And_intro B A

updatePart1 : List Symbols -> List (And Symbols Symbols)
updatePart1 d = customMap thueMorseFn d

updatePart2 : List (And Symbols Symbols) -> List Symbols
updatePart2 [] = []
updatePart2 ((And_intro x y) :: zs) = x :: (y :: (updatePart2 zs))

updater : List Symbols -> List Symbols
updater d = updatePart2 (updatePart1 d)

repeat : (a -> a) -> a -> Nat -> a
repeat f start Z = start
repeat f start (S t) = f (repeat f start t)

thueMorseSequence : List Symbols
thueMorseSequence = repeat updater [A] 5
