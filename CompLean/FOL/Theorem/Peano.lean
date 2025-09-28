/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import CompLean.FOL.Definitions.Formula
import CompLean.FOL.Definitions.Theory
import CompLean.FOL.Examples.Peano

open FOL Lang Term Peano

section Test

abbrev V := Empty ⊕ ℕ

instance : OfNat V 1 where
  ofNat := Sum.inr 1

#check ?0
#check (?0 : peano.Term V)
#check (?1 : peano.Term V)
#check (0 : peano.Term V)
#check (succOp.apply₁ 0)
#check (succOp.apply₁ (?1 : peano.Term V))

theorem test1 : (?0 : peano.Term V) = var (Sum.inr 0) := by
  rfl

theorem varFinset_example : varFinset (I:= ℕ) (0 + ((succOp.apply₁ 0))) = ∅ := by
  rfl

theorem varFinset_example2 : varFinset (I:= V) (0 + succOp.apply₁ ?1) = {1} := by
  rfl

end Test
