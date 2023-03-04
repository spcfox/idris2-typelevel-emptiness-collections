module Spec

import Data.CheckedEmpty.List.Lazy

--- Examples ---

0 e_f_0 : LazyLst False Nat
e_f_0 = []

0 e_f_2 : LazyLst False Nat
e_f_2 = [1, 2]

0 e_f_5 : LazyLst False Nat
e_f_5 = [1, 2, 3, 4, 5]

0 e_f_a : LazyLst False Nat
e_f_a = 0 :: e_f_5

failing

  0 e_t_0 : LazyLst True Nat
  e_t_0 = []

0 e_t_2 : LazyLst True Nat
e_t_2 = [1, 2]

0 e_t_5 : LazyLst True Nat
e_t_5 = [1, 2, 3, 4, 5]

0 e_t_a : LazyLst True Nat
e_t_a = 0 :: e_t_5
