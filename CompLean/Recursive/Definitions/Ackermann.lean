/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import CompLean.Recursive.Definitions.Prelim
import CompLean.Recursive.Definitions.PrimRec

def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

#eval ack 1 2

#eval ack 2 2

#eval ack 3 2

#eval ack 3 3
