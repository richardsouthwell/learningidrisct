module Main

hello : String -> String
hello name = "Hello " ++ name

a : Int
a = 6

addThree : Int -> Int
addThree x = 3 + x


main : IO ()
main = putStrLn  "Hello world"

-- to convert this idris code to javascript do...
-- idris --codegen javascript richardTest.idr -o richardTest.js