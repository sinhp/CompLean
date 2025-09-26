import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/-! # The single

We represent a language as a pair of ℕ-indexed families of types, each of which is to be
thought of as the collection of operation and relation symbols stratified by arity.

Examples:
* The language of groups has one binary operation symbol (multiplication), one unary operation
  symbol (inversion), and one constant symbol (the identity element).
* The language of (ordered) rings has two binary operation symbols (addition and multiplication),
  two unary operation symbols (additive inverse and multiplicative inverse), two constant symbols
  (additive and multiplicative identities), and one binary relation symbol (the order relation).
-/


namespace FOL

/-! # Langs and Structures -/

abbrev Arity := ℕ

/-- The type of n-tuples of elements of a given type `M`. -/
abbrev tuple (n : Arity) (M : Type w) := Fin n → M

/-- A __single sorted first-order language__ consists of a type of operation symbols of every natural-number arity and a
  type of relation symbols of every natural-number arity. -/
structure Lang.{u,v} where
  /-- For every arity, a `Type*` of function symbols of that arity -/
  Ops : Arity → Type u
  /-- For every arity, a `Type*` of relation symbols of that arity -/
  Rels : Arity → Type v

namespace Lang

variable (L : Lang.{u, v})

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

/-- Passes a `DecidableEq` instance on a type of operation symbols through the  `Lang`
constructor. -/
instance instDecidableEqFunctions {m : ℕ → Type*} {R : ℕ → Type*} (n : ℕ) [DecidableEq (m n)] :
    DecidableEq ((⟨m, R⟩ : Lang).Ops n) := inferInstance

/-- A language is finite if it has finitely many symbols. -/
def IsFinite := Finite L.Symbols

/-- The sum of two languages consists of the disjoint union of their symbols. -/
protected def sum (L' : Lang.{u', v'}) : Lang :=
  ⟨fun n => L.Ops n ⊕ L'.Ops n, fun n => L.Rels n ⊕ L'.Rels n⟩

end Lang

end FOL
