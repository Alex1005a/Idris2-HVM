module Main

import Test.Golden

idris2HVMTests : TestPool
idris2HVMTests = MkTestPool "hvm" [] Nothing [
    "hello-world", "fib", "reduce-term"
    ]

main : IO ()
main = runner [testPaths "hvm" idris2HVMTests]
    where
        testPaths : String -> TestPool -> TestPool
        testPaths dir = { testCases $= map ((dir ++ "/") ++) }