module Main

hello : String -> String
hello name = "Hello " ++ name



main : IO ()
main = putStrLn  "Hello world"