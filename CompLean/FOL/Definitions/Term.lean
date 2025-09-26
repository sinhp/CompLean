import CompLean.FOL.Definitions.Language


/-! # The definition of terms in first-order logic

Terms are defined inductively as either variables or the application of an operation symbol to a
tuple of terms. Note that it is impossible to produce an ill-formed term or formula,
because type-correctness is equivalent to well-formedness.
This eliminates the need for separate well-formedness proofs.
-/

namespace FOL.Lang

universe u v u' v' u'' v''

variable (L : Lang.{u, v})

/-- A term on `I` is either
- `v i`, i.e. a variable indexed by an element of `i : I`, or
- or `m t₁ ... tₙ`, i.e. an operation symbol `m` applied to simpler terms `t₁, ..., tₙ`. -/
inductive Term (I : Type u') : Type max u u'
  | var (i : I) : Term I
  | op {n : Arity} (_m : L.Ops n) (_ts : Fin n → Term I) : Term I
export Term (var op)

variable {I : Type u'}

variable {L : Lang.{u, v}}

/-- A constant symbol can be seen as a term. -/
def Constants.term (c : L.Constants) : L.Term I :=
  op c default

/-- Applies a unary function to a term. -/
def Ops.apply₁ (f : L.Ops 1) (t : L.Term I) : L.Term I :=
  op f ![t]

/-- Applies a binary function to two terms. -/
def Ops.apply₂ (f : L.Ops 2) (t₁ t₂ : L.Term I) : L.Term I :=
  op f ![t₁, t₂]

/-- If the variables are inhabited, then the terms are also inhabited. -/
instance inhabitedOfVar [Inhabited I] : Inhabited (L.Term I) :=
  ⟨var default⟩

/-- If the language has at least one constant, then the terms are inhabited. -/
instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term I) :=
  ⟨(default : L.Constants).term⟩


namespace Term

variable {J : Type u''} {K : Type v''}

/-- Substitutes the variables in a given term with terms.
e.g. if `t = m v₁ v₂` and we substitute `v₁` with `g(v₃)` and `v₂` with `v₄`,
we get `t' = m (g(v₃)) (v₄)`, that is `(t.subst f) = m (f(1)) (f(2))` where `f` is defined by
`f(1) = g(v₃)` and `f(2) = v₄`. -/
@[simp]
def subst : L.Term I → (I → L.Term J) → L.Term J
  | var i, tf => tf i
  | op m ts, tf => op m fun i => (ts i).subst tf

/-- Relabels a term's variables along a particular function. -/
@[simp]
def relabel (g : I → J) : L.Term I → L.Term J
  | var i => var (g i)
  | op m ts => op m fun {i} => (ts i).relabel g

theorem relabel_id (t : L.Term I) : t.relabel id = t := by
  induction t with
  | var => rfl
  | op m ts ih => simp only [relabel, ih]

@[simp]
theorem relabel_id_eq_id : (Term.relabel id : L.Term I → L.Term I) = id :=
  funext relabel_id

@[simp]
theorem relabel_relabel (f : I → J) (g : J → K) (t : L.Term I) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction t with
  | var => rfl
  | op m ts ih => simp [ih]

@[simp]
theorem relabel_comp_relabel (f : I → J) (g : J → K) :
    (Term.relabel g ∘ Term.relabel f : L.Term I → L.Term K) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : I ≃ J) : L.Term I ≃ L.Term J :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

end Term

namespace Term

open Finset

/-- The `Finset` of variables used in a given term. -/
@[simp]
def varFinset [DecidableEq I] : L.Term I → Finset I
  | var i => {i}
  | op _m ts => univ.biUnion fun i => (ts i).varFinset

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft [DecidableEq I] {J : Type u''} : L.Term (I ⊕ J) → Finset I
  | var (Sum.inl i) => {i}
  | var (Sum.inr _i) => ∅
  | op _f ts => univ.biUnion fun i => (ts i).varFinsetLeft

end Term

end FOL.Lang
