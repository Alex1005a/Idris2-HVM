module Main

fib : Nat -> Nat
fib 0 = 0
fib 1 = 1
fib (S n@(S m)) = fib n + fib m

main : IO ()
main = print $ fib 10