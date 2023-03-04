module Spec

import Data.CheckedEmpty.List.Lazy

import Debug.Trace

foldlM' : Monad m => (fm : b -> a -> m b) -> (init : b) -> LazyLst ne a -> m b
foldlM' fm init xs = foldrLazy (\x, k, z => fm z x >>= k) pure xs init

l : LazyLst1 Nat
l = (\n => trace "gen \{show n}" n) <$> iterateN 10000 S Z

-- Both should be actually short-cutting (i.e., not many `gen *` should be printed)

x : Lazy (Maybe Nat)
x = foldlM' (\m, n => if m <= 1 then Just n else Nothing) 0 l

y : Lazy (Maybe Nat)
y = foldlM (\m, n => if m <= 1 then Just n else Nothing) 0 l

main : IO ()
main = do
  putStrLn "----------"
  putStrLn $ show x
  putStrLn "----------"
  putStrLn $ show y
  putStrLn "----------"
