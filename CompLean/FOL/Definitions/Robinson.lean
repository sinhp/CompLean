/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import CompLean.FOL.Definitions.Basic

/-!
# Robinson Arithmetic
-/

variable {V : Type*} -- The type of variables

namespace FOL

open Language

/-- The inductive type of Robinson arithmetic function symbols. -/
inductive RobinsonOps : Arity → Type
  | zero : RobinsonOps 0
  | succ : RobinsonOps 1
  | add : RobinsonOps 2
  | mul : RobinsonOps 2
  deriving DecidableEq

/-- The language of Robinson arithmetic, defined as (0, S, +, ×). -/
def Language.robinson : Language where
  Ops := RobinsonOps
  Rels := fun _ => Empty
  deriving IsAlgebraic

namespace Robinson

open RobinsonOps

example (n : ℕ) : DecidableEq (robinson.Ops n) := inferInstance

example (n : ℕ) : DecidableEq (robinson.Ops n) := inferInstance

/-- `RobinsonOps.zero`, but with the defeq type `Language.robinson.Ops 0` instead of `RobinsonOps 0` -/
abbrev zeroOp : robinson.Ops 0 := zero

/-- `RobinsonOps.succ`, but with the defeq type `Language.robinson.Ops 1` instead of `RobinsonOps 1` -/
abbrev succOp : robinson.Ops 1 := succ

/-- `RobinsonOps.add`, but with the defeq type `Language.robinson.Ops 2` instead
of `RobinsonOps 2` -/
abbrev addOp : robinson.Ops 2 := add

/-- `RobinsonOps.mul`, but with the defeq type `Language.robinson.Ops 2` instead
of `RobinsonOps 2` -/
abbrev mulOp : robinson.Ops 2 := mul

variable {t t₁ t₂ : robinson.Term V}

instance : Zero (robinson.Term V) where
  zero := Constants.term .zero

instance : Add (robinson.Term V) where
  add := Ops.apply₂ .add

instance : Mul (robinson.Term V) where
  mul := Ops.apply₂ .mul

/-- Addition of a term `t` to itself `n` times, `nsmulRec n a = a+a+...+a`. -/
instance : SMul ℕ (robinson.Term V) where
  smul := nsmulRec

instance : Fintype robinson.Symbols :=
  ⟨⟨Multiset.ofList
      [Sum.inl ⟨2, .add⟩,
       Sum.inl ⟨2, .mul⟩,
       Sum.inl ⟨1, .succ⟩,
       Sum.inl ⟨0, .zero⟩], by
    dsimp [Language.Symbols]; decide⟩, by
    intro x
    dsimp [Language.Symbols]
    rcases x with ⟨_, f⟩ | ⟨_, f⟩
    · cases f <;> decide
    · cases f ⟩

@[simp] theorem zero_nsmul : 0 • t = 0 := rfl

@[simp] theorem succ_nsmul {n : ℕ} : (n + 1) • t = n • t + t := rfl

/-- Summation over a finite set of terms in Robinson arithmetic.

It is defined via choice, so the result only makes sense when the structure satisfies
commutativity (see `realize_sum`). -/
noncomputable def sum {β : Type*} (s : Finset β) (f : β → robinson.Term V) : robinson.Term V :=
  (s.toList.map f).sum

variable {M : Type*} {v : V → M}

section

variable [Zero M] [One M] [Add M] [Mul M]

instance : robinson.Structure M where
  opMap
  | .zero, _ => 0
  | .add, v => v 0 + v 1
  | .succ, v => v 0 + 1
  | .mul, v => v 0 * v 1

@[simp] theorem funMap_zero {v} :
    Structure.opMap (L := robinson) (M := M) RobinsonOps.zero v = 0 := rfl

@[simp] theorem funMap_add {v} :
    Structure.opMap (L := robinson) (M := M) RobinsonOps.add v = v 0 + v 1 := rfl

@[simp] theorem funMap_succ {v} :
    Structure.opMap (L := robinson) (M := M) RobinsonOps.succ v = v 0 + 1 := rfl

@[simp] theorem funMap_mul {v} :
    Structure.opMap (L := robinson) (M := M) RobinsonOps.mul v = v 0 * v 1 := rfl

@[simp] theorem realize_zero :
    Term.realize (L := robinson) (M := M) v 0 = 0 := rfl

@[simp] theorem realize_add :
    Term.realize (L := robinson) (M := M) v (t₁ + t₂) =
    Term.realize (L := robinson) (M := M) v t₁ + Term.realize (L := robinson) (M := M) v t₂ := rfl

@[simp] theorem realize_mul :
    Term.realize (L := robinson) (M := M) v (t₁ * t₂) =
    Term.realize (L := robinson) (M := M) v t₁ * Term.realize (L := robinson) (M := M) v t₂ := rfl

end

end Robinson

end FOL
