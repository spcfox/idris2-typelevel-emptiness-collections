module Runner

import BaseDir

import Test.Golden.RunnerHelper

CmdUnderTest where
  cmdUnderTest = baseTestsDir ++ "/.pack_lock"

main : IO ()
main = goldenRunner
  [ "Musthave typechecks"           `atDir` "typechecks"
  , "Documentation"                 `atDir` "docs"
  ]
