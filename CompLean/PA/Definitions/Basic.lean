/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import CompLean.FOL.Definitions.Basic

/-!
# Peano arithmetic
-/

variable {V : Type*} -- The type of variables

namespace FOL

open Language

/-- The inductive type of Peano arithmetic function symbols. -/
inductive PAOps : Arity → Type
  | zero : PAOps 0
  | succ : PAOps 1
  | add : PAOps 2
  | mul : PAOps 2
  deriving DecidableEq

/-- The language of Peano arithmetic, defined as (0, S, +, ×). -/
def Language.peano : Language where
  Ops := PAOps
  Rels := fun _ => Empty
  deriving IsAlgebraic

namespace Language.peano

variable {t t₁ t₂ : peano.Term V}

instance : Zero (peano.Term V) where
  zero := Constants.term .zero

instance : Add (peano.Term V) where
  add := Ops.apply₂ .add

instance : Mul (peano.Term V) where
  mul := Ops.apply₂ .mul

/-- Addition of a term `t` to itself `n` times, `nsmulRec n a = a+a+...+a`. -/
instance : SMul ℕ (peano.Term V) where
  smul := nsmulRec

@[simp] theorem zero_nsmul : 0 • t = 0 := rfl

@[simp] theorem succ_nsmul {n : ℕ} : (n + 1) • t = n • t + t := rfl

/-- Summation over a finite set of terms in peano arithmetic.

It is defined via choice, so the result only makes sense when the structure satisfies
commutativity (see `realize_sum`). -/
noncomputable def sum {β : Type*} (s : Finset β) (f : β → peano.Term V) : peano.Term V :=
  (s.toList.map f).sum

variable {M : Type*} {v : V → M}

section

variable [Zero M] [One M] [Add M] [Mul M]

instance : peano.Structure M where
  opMap
  | .zero, _ => 0
  | .add, v => v 0 + v 1
  | .succ, v => v 0 + 1
  | .mul, v => v 0 * v 1

@[simp] theorem funMap_zero {v} :
    Structure.opMap (L := peano) (M := M) PAOps.zero v = 0 := rfl

@[simp] theorem funMap_add {v} :
    Structure.opMap (L := peano) (M := M) PAOps.add v = v 0 + v 1 := rfl

@[simp] theorem funMap_succ {v} :
    Structure.opMap (L := peano) (M := M) PAOps.succ v = v 0 + 1 := rfl

@[simp] theorem funMap_mul {v} :
    Structure.opMap (L := peano) (M := M) PAOps.mul v = v 0 * v 1 := rfl

@[simp] theorem realize_zero : Term.realize v (0 : peano.Term V) = 0 := rfl

@[simp] theorem realize_one : Term.realize v (1 : peano.Term V) = 1 := rfl

@[simp] theorem realize_add :
    Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := rfl

end

@[simp] theorem realize_natCast [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n : peano.Term V) = n := by
  induction n with simp [*]

@[simp] theorem realize_nsmul [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n • t) = n • Term.realize v t := by
  induction n with simp [*, add_nsmul]

@[simp] theorem realize_sum [AddCommMonoidWithOne M]
    {β : Type*} {s : Finset β} {f : β → peano.Term V} :
    Term.realize v (sum s f) = ∑ i ∈ s, Term.realize v (f i) := by
  classical
  simp only [sum]
  conv => rhs; rw [← s.toList_toFinset, List.sum_toFinset _ s.nodup_toList]
  generalize s.toList = l
  induction l with simp [*]

end FOL
