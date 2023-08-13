module Main

main : IO ()
main = print $ reverse $ unpack "Hello world!"