module Spec

import Data.CheckedEmpty.List.Lazy

import Debug.Trace

ll : LazyL'st1 Nat
ll = iterateN 10000 (traceValBy (("after addition " ++) . show) . S) (trace "initial ll" Z)

llf : Nat -> LazyL'st1 String
llf st = iterateN 10000 (traceValBy ("after stringification" ++) . (++ "'")) (trace "initial llf from \{show st}" "n:\{show st}")

main : IO ()
main = do
  let llllf = ll >>= llf
  putStrLn "intermediate"
  putStrLn $ show $ take 5 llllf
