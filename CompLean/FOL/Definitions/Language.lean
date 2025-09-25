import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

import Mathlib

universe u v u' v' w w' u₁ v₁

namespace FOL

/-! # Languages and Structures -/

abbrev Arity := ℕ

/-- The type of n-tuples of elements of a given type `M`. -/
abbrev tuple (n : Arity) (M : Type w) := Fin n → M

/-- A __single sorted first-order language__ consists of a type of operation symbols of every natural-number arity and a
  type of relation symbols of every natural-number arity. -/
@[nolint checkUnivs]
structure Language where
  /-- For every arity, a `Type*` of function symbols of that arity -/
  Ops : Arity → Type u
  /-- For every arity, a `Type*` of relation symbols of that arity -/
  Rels : Arity → Type v

namespace Language

variable (L : Language.{u, v})

/-- A language is _algebraic_ when it has no relation symbols. -/
abbrev IsAlgebraic : Prop := ∀ n, IsEmpty (L.Rels n)

/-- A language is _relational_ when it has no function symbols. -/
abbrev IsRelational : Prop := ∀ n, IsEmpty (L.Ops n)

/-- The type of symbols in a given language. -/
abbrev Symbols :=
  (Σ l, L.Ops l) ⊕ (Σ l, L.Rels l)

/-- The type of constants in a given language. -/
protected abbrev Constants :=
  L.Ops 0

/-- The type of propositions in a given language. -/
protected abbrev Propositions :=
  L.Rels 0

/-- Passes a `DecidableEq` instance on a type of operation symbols through the  `Language`
constructor. -/
instance instDecidableEqFunctions {m : ℕ → Type*} {R : ℕ → Type*} (n : ℕ) [DecidableEq (m n)] :
    DecidableEq ((⟨m, R⟩ : Language).Ops n) := inferInstance

end Language

end FOL
