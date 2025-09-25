import CompLean.FOL.Definitions.Language

namespace FOL.Language

variable (L : Language.{u, v})

/-- A term on `I` is either
- `v i`, i.e. a variable indexed by an element of `i : I`, or
- or `m t₁ ... tₙ`, i.e. an operation symbol `m` applied to simpler terms `t₁, ..., tₙ`. -/
inductive Term (I : Type u') : Type max u u'
  | var (i : I) : Term I
  | op {n : Arity} (_m : L.Ops n) (_ts : Fin n → Term I) : Term I
export Term (var op)

variable {I J : Type u₁}

variable {L}

/-- A constant symbol can be seen as a term. -/
def Constants.term (c : L.Constants) : L.Term I :=
  op c default

/-- Applies a unary function to a term. -/
def Ops.apply₁ (f : L.Ops 1) (t : L.Term I) : L.Term I :=
  op f ![t]

/-- Applies a binary function to two terms. -/
def Ops.apply₂ (f : L.Ops 2) (t₁ t₂ : L.Term I) : L.Term I :=
  op f ![t₁, t₂]

/-- Substitutes the variables in a given term with terms. -/
@[simp]
def Term.subst : L.Term I → (I → L.Term J) → L.Term J
  | var a, tf => tf a
  | op f ts, tf => op f fun i => (ts i).subst tf

end FOL.Language
