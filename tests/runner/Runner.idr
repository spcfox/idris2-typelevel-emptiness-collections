module Runner

import BaseDir

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Musthave typechecks"           `atDir` "typechecks"
  , "Documentation"                 `atDir` "docs"
  ]
