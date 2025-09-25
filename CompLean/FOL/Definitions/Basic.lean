import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

import Mathlib

universe u v u' v' w w' u₁ v₁

namespace FOL

/-! # Languages and Structures -/

abbrev Arity := ℕ

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

/-- The type of n-tuples of elements of a given type `M`. -/
abbrev tuple (n : Arity) (M : Type w) := Fin n → M

/-- A first-order __structure__ on a type `M`, considered as the base (aka underlying set) of the strucuture, consists of interpretations of all
the symbols in a given language. Each operation of arity `n` is interpreted as a function sending tuples of length `n` to `M`, and
a relation of arity `n` a set of the tuples of length `n`.  -/
@[ext]
class Structure (M : Type w) where
  /-- Interpretation of the operation symbols -/
  opMap : ∀ {n}, L.Ops n → (tuple n M) → M := by
    exact fun {n} => isEmptyElim -- if there is no function symbols of arity `n`, return nothing by default.
  /-- Interpretation of the relation symbols -/
  relMap : ∀ {n}, L.Rels n → Set (tuple n M) := by
    exact fun {n} => isEmptyElim -- if there is no relation symbols of arity `n`, return nothing by default.


variable (M : Type w) (N : Type w') [L.Structure M] [L.Structure N]

open Structure

variable {M}

/-- A term `t` with variables indexed by `I` can be evaluated by giving a value to each variable. -/
def Term.realize (v : I → M) : ∀ _t : L.Term I, M
  | var k => v k
  | op m ts => opMap m fun i => (ts i).realize v

open Structure

/-- Used for defining `FirstOrder.Language.Theory.ModelType.instInhabited`. -/
def Inhabited.trivialStructure [Inhabited M] : L.Structure M :=
  ⟨default, default⟩

variable (M)

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of Operations and maps tuples in one structure where a given relation is sati to
  tuples in the second structure where that relation is still true. -/
structure Hom where
  /-- The underlying function of a homomorphism of structures -/
  toFun : M → N
  /-- The homomorphism commutes with the interpretations of the function symbols -/
  map_op' : ∀ {n} (f : L.Ops n) (x), toFun (opMap f x) = opMap f (toFun ∘ x) := by
    intros; trivial
  /-- The homomorphism sends related elements to related elements -/
  map_rel' : ∀ {n} (r : L.Rels n) (x), relMap r x → relMap r (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " →[" L "] " B => FirstOrder.Language.Hom L A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} (f : L.Ops n) (x), toFun (opMap f x) = opMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Rels n) (x), relMap r (toFun ∘ x) ↔ relMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} (f : L.Ops n) (x), toFun (opMap f x) = opMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Rels n) (x), relMap r (toFun ∘ x) ↔ relMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

variable {N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

/-- Interpretation of a constant symbol -/
@[coe]
def constantMap (c : L.Constants) : M := opMap c (default : tuple 0 M)

-- instance : CoeTC L.Constants M :=
--   ⟨constantMap⟩

end Language

end FOL
