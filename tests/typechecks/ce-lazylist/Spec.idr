module Spec

import Data.CheckedEmpty.List.Lazy

--- Examples ---

0 e_f_0 : LazyL'st False Nat
e_f_0 = []

0 e_f_2 : LazyL'st False Nat
e_f_2 = [1, 2]

0 e_f_5 : LazyL'st False Nat
e_f_5 = [1, 2, 3, 4, 5]

0 e_f_a : LazyL'st False Nat
e_f_a = 0 :: e_f_5

failing

  0 e_t_0 : LazyL'st True Nat
  e_t_0 = []

0 e_t_2 : LazyL'st True Nat
e_t_2 = [1, 2]

0 e_t_5 : LazyL'st True Nat
e_t_5 = [1, 2, 3, 4, 5]

0 e_t_a : LazyL'st True Nat
e_t_a = 0 :: e_t_5
