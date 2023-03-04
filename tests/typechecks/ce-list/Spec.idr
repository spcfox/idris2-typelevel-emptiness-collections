module Spec

import Data.CheckedEmpty.List

--- Examples ---

0 e_f_0 : Lst False Nat
e_f_0 = []

0 e_f_2 : Lst False Nat
e_f_2 = [1, 2]

0 e_f_5 : Lst False Nat
e_f_5 = [1, 2, 3, 4, 5]

0 e_f_a : Lst False Nat
e_f_a = 0 :: e_f_5

failing

  0 e_t_0 : Lst True Nat
  e_t_0 = []

0 e_t_2 : Lst True Nat
e_t_2 = [1, 2]

0 e_t_5 : Lst True Nat
e_t_5 = [1, 2, 3, 4, 5]

0 e_t_a : Lst True Nat
e_t_a = 0 :: e_t_5
