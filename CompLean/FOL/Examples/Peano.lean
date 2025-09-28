/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import CompLean.FOL.Definitions.Formula
import CompLean.FOL.Definitions.Theory

/-!
# Peano Arithmetic
-/

variable {I : Type u'} -- The type of variables

namespace FOL

open Lang BdForm

/-- The inductive type of Peano arithmetic function symbols. -/
inductive PeanoOps : Arity → Type
  | zero : PeanoOps 0
  | succ : PeanoOps 1
  | add : PeanoOps 2
  | mul : PeanoOps 2
  deriving DecidableEq

/-- The language of Peano arithmetic, defined as (0, S, +, ×). -/
def Lang.peano : Lang where
  Ops := PeanoOps
  Rels := fun _ => Empty
  deriving IsAlgebraic

namespace Peano

open PeanoOps

example (n : ℕ) : DecidableEq (Lang.peano.Ops n) := inferInstance

example (n : ℕ) : DecidableEq (Lang.peano.Ops n) := inferInstance

/-- `PeanoOps.zero`, but with the defeq type `Language.peano.Ops 0` instead of `PeanoOps 0` -/
abbrev zeroOp : peano.Ops 0 := zero

/-- `PeanoOps.succ`, but with the defeq type `Language.peano.Ops 1` instead of `PeanoOps 1` -/
abbrev succOp : peano.Ops 1 := succ

/-- `PeanoOps.add`, but with the defeq type `Language.peano.Ops 2` instead
of `PeanoOps 2` -/
abbrev addOp : peano.Ops 2 := add

/-- `PeanoOps.mul`, but with the defeq type `Language.peano.Ops 2` instead
of `PeanoOps 2` -/
abbrev mulOp : peano.Ops 2 := mul

variable {t t₁ t₂ : peano.Term I}

instance : Zero (peano.Term I) where
  zero := Constants.term .zero

instance : Add (peano.Term I) where
  add := Ops.apply₂ .add

instance : Mul (peano.Term I) where
  mul := Ops.apply₂ .mul

/-- Addition of a term `t` to itself `n` times, `nsmulRec n a = a+a+...+a`. -/
instance : SMul ℕ (peano.Term I) where
  smul := nsmulRec

instance : Fintype peano.Symbols :=
  ⟨⟨Multiset.ofList
      [Sum.inl ⟨2, .add⟩,
       Sum.inl ⟨2, .mul⟩,
       Sum.inl ⟨1, .succ⟩,
       Sum.inl ⟨0, .zero⟩], by
    dsimp [Lang.Symbols]; decide⟩, by
    intro x
    dsimp [Lang.Symbols]
    rcases x with ⟨_, f⟩ | ⟨_, f⟩
    · cases f <;> decide
    · cases f ⟩

@[simp] theorem zero_nsmul : 0 • t = 0 := rfl

@[simp] theorem succ_nsmul {n : ℕ} : (n + 1) • t = n • t + t := rfl

/-- Summation over a finite set of terms in Peano arithmetic.

It is defined via choice, so the result only makes sense when the structure satisfies
commutativity (see `realize_sum`). -/
noncomputable def sum {β : Type*} (s : Finset β) (f : β → peano.Term I) : peano.Term I :=
  (s.toList.map f).sum

variable {M : Type*} {v : I → M}

section

variable [Zero M] [One M] [Add M] [Mul M]

instance : peano.Structure M where
  opMap
  | .zero, _ => 0
  | .add, v => v 0 + v 1
  | .succ, v => v 0 + 1
  | .mul, v => v 0 * v 1

@[simp] theorem funMap_zero {v} :
    Structure.opMap (L := peano) (M := M) PeanoOps.zero v = 0 := rfl

@[simp] theorem funMap_add {v} :
    Structure.opMap (L := peano) (M := M) PeanoOps.add v = v 0 + v 1 := rfl

@[simp] theorem funMap_succ {v} :
    Structure.opMap (L := peano) (M := M) PeanoOps.succ v = v 0 + 1 := rfl

@[simp] theorem funMap_mul {v} :
    Structure.opMap (L := peano) (M := M) PeanoOps.mul v = v 0 * v 1 := rfl

@[simp] theorem realize_zero :
    Term.realize (L := peano) (M := M) v 0 = 0 := rfl

@[simp] theorem realize_add :
    Term.realize (L := peano) (M := M) v (t₁ + t₂) =
    Term.realize (L := peano) (M := M) v t₁ + Term.realize (L := peano) (M := M) v t₂ := rfl

@[simp] theorem realize_mul :
    Term.realize (L := peano) (M := M) v (t₁ * t₂) =
    Term.realize (L := peano) (M := M) v t₁ * Term.realize (L := peano) (M := M) v t₂ := rfl

end

end Peano

open Peano

#check Nat.succ_ne_zero
#check Nat.eq_zero_or_eq_succ_pred
#check Nat.succ_inj
#check Nat.add_zero
#check Nat.add_succ
#check Nat.mul_zero
#check Nat.mul_succ

inductive RobinsonAxioms : Type
  | succ_ne_zero : RobinsonAxioms
  | eq_zero_or_eq_succ_pred : RobinsonAxioms
  | succ_inj : RobinsonAxioms
  | add_zero : RobinsonAxioms
  | add_succ : RobinsonAxioms
  | mul_zero : RobinsonAxioms
  | mul_succ : RobinsonAxioms

-- #check FunLike

@[simp]
def RobinsonAxioms.toSentence : RobinsonAxioms → Lang.peano.Sentence
  | .succ_ne_zero => ∀' ∼(succOp.apply₁ ?0 =' 0)
  | .eq_zero_or_eq_succ_pred => ∀' ∃' (∼(?0 =' 0) ⟹  succOp.apply₁ (?1) =' ?0)
  | .succ_inj => ∀' ∀' (succOp.apply₁ (?0) =' succOp.apply₁ (?1) ⟹ ?0 =' ?1)
  | .add_zero => ∀' ((?0 + 0) =' ?0)
  | .add_succ => ∀' ∀' ((?0 + succOp.apply₁ (?1)) =' succOp.apply₁ (?0 + ?1))
  | .mul_zero => ∀' ((?0 * 0) =' 0)
  | .mul_succ => ∀' ∀' ((?0 * succOp.apply₁ (?1)) =' (?0 * ?1 + ?0))

/-- The first order theory of fields, as a theory over the language of rings -/
def Lang.Theory.robinson : peano.Theory :=
  Set.range RobinsonAxioms.toSentence

-- Prove the following 24 facts in the theory of Robinson arithmetic:


end FOL
