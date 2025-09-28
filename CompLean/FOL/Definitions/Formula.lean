import CompLean.FOL.Definitions.Structure

/-! # Formulas in First-Order Logic

`BForm` is a type that represents first-order logic _bounded formulas_.

They should not be confused with bounded quantifiers, appearing for instance in `Δ₀` formulas in arithmetic hierarchy. Instead, here "bounded" refers to the way bound variables are handled in the formulas using a modified version of de Bruijn variables.

More specifically, `L.BForm I n` represents a formula where:
- `I` indexes "free variables" that cannot be quantified over
- `n` (a natural number) represents the number of additional variables indexed by `Fin n` that **can** be quantified over

## The Structure

From the inductive definition, a `BForm I n` can be:
1. `falsum` - the false formula (⊥)
2. `equal t₁ t₂` - equality between two terms
3. `rel R ts` - a relation applied to terms
4. `imp f₁ f₂` - implication between formulas
5. `all f` - universal quantification (∀)

## Examples in First-Order Logic

Let me give some concrete examples:

### Example 1: Simple Formula
Consider the formula `∀v₀. P(v₀)` in standard notation.
- This would be represented as `BForm Empty 0`
- The `v₀` is handled internally using the de Bruijn index system
- Since we're quantifying over all variables, `n = 0` (no unquantified Fin-indexed variables remain)

### Example 2: Formula with Free Variables
Consider `P(a) ∧ ∀v₀. Q(v₀, a)` where `a` is a free variable.
- This might be `BForm α 0` where `I` contains the index for `a`
- The `a` stays free (indexed by `I`), while `v₀` gets bound by the quantifier

### Example 3: Partially Quantified Formula
Consider a formula `P(v₀, y)` where we want to later quantify over `v₀` but keep `y` free.
- This could be `BForm I 1` where:
  - `I` indexes `y` (the variable that stays free)
  - The `1` indicates there's one variable (indexed by `Fin 1`) that could be quantified over
  - To get `∀v₀. P(v₀, y)`, you'd apply the `all` constructor

### Example 4: The Quantification Process
The comment explains: "For any `φ : L.BForm α (n + 1)`, we define the formula `∀' φ : L.BForm α n`
by universally quantifying over the variable indexed by `n : Fin (n + 1)`."

So if you have:
- `φ : BForm α 2` representing something like `P(v₀, v₁, a)`
- `∀' φ : BForm α 1` represents `∀v₀. P(v₀, v₁, a)`
- `∀' (∀' φ) : BForm α 0` represents `∀v₀. ∀v₁. P(v₀, v₁, a)`

## Formulas from BForms

A formula is a bounded formula with no `Fin`-indexed variables, i.e., `L.BForm I 0`. This means all variables are indexed by `I` and are free.

A _sentence_ is a formula with no free variables, i.e., `L.BForm Empty 0`.
For instance in the language of monoids, the formula `∀x ∀y (x * y = y * x)` is a sentence
asserting commutativity condition, and in ZF set theory,
the formula `∀ s ∃ t ∀ x (x ∈ t ↔ ∀ y (y ∈ x → y ∈ s))` is a sentence
asserting the existence of power sets.
-/


universe u v w u' v'

namespace FOL.Lang

variable (L : Lang.{u, v}) (I : Type u')

/-- `BdForm α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BdForm : ℕ → Type max u v u'
  | falsum {n} : BdForm n
  | equal {n} (t₁ t₂ : L.Term (I ⊕ (Fin n))) : BdForm n
  | rel {n m : ℕ} (R : L.Rels m) (ts : Fin m → L.Term (I ⊕ (Fin n))) : BdForm n
  /-- The implication between two bounded formulas -/
  | imp {n} (f₁ f₂ : BdForm n) : BdForm n
  /-- The universal quantifier over bounded formulas -/
  | all {n} (f : BdForm (n + 1)) : BdForm n

open BdForm

/-- `Form I` is the type of formulas with all free variables indexed by `I`. -/
abbrev Form :=
  L.BdForm I 0

/-- A sentence is a formula with no free variables. -/
abbrev Sentence :=
  L.Form Empty

variable {L} {I} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def Rels.bdForm {m : ℕ} (R : L.Rels n) (ts : Fin n → L.Term (I ⊕ (Fin m))) :
    L.BdForm I m :=
  BdForm.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Rels.bdForm₁ (r : L.Rels 1) (t : L.Term (I ⊕ (Fin n))) :
    L.BdForm I n :=
  r.bdForm ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
def Rels.bdForm₂ (r : L.Rels 2) (t₁ t₂ : L.Term (I ⊕ (Fin n))) :
    L.BdForm I n :=
  r.bdForm ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (I ⊕ (Fin n))) : L.BdForm I n :=
  BdForm.equal t₁ t₂

/-- Applies a relation to terms as a bounded formula. -/
def Rels.form (R : L.Rels n) (ts : Fin n → L.Term I) : L.Form I :=
  R.bdForm fun i => (ts i).relabel Sum.inl

/-- Applies a unary relation to a term as a formula. -/
def Rels.form₁ (r : L.Rels 1) (t : L.Term I) : L.Form I :=
  r.form ![t]

/-- Applies a binary relation to two terms as a formula. -/
def Rels.form₂ (r : L.Rels 2) (t₁ t₂ : L.Term I) : L.Form I :=
  r.form ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term I) : L.Form I :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BdForm

instance : Inhabited (L.BdForm I n) :=
  ⟨falsum⟩

instance : Bot (L.BdForm I n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BdForm I n) : L.BdForm I n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex (φ : L.BdForm I (n + 1)) : L.BdForm I n :=
  φ.not.all.not

instance : Top (L.BdForm I n) :=
  ⟨BdForm.not ⊥⟩

instance : Min (L.BdForm I n) :=
  ⟨fun f g => (f.imp g.not).not⟩

instance : Max (L.BdForm I n) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BdForm I n) : L.BdForm I n :=
  φ.imp ψ ⊓ ψ.imp φ

open Finset

/-- The `Finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq I] : ∀ {n}, L.BdForm I n → Finset I
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp φ₁ φ₂ => φ₁.freeVarFinset ∪ φ₂.freeVarFinset
  | _n, all φ => φ.freeVarFinset

/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`.
e.g. if `φ : L.BoundedFormula α 2` represents `P(v₀, v₁, a)`, then
`φ.castLE (by decide) : L.BoundedFormula α 3` represents the same formula `P(v₀, v₁, v₂, a)`.
where `v₂` is an additional variable that is not used in the formula. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BdForm I m → L.BdForm I n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp φ₁ φ₂ => (φ₁.castLE h).imp (φ₂.castLE h)
  | _m, _n, h, all φ => (φ.castLE (add_le_add_right h 1)).all

/-- Places universal quantifiers on all extra variables of a bounded formula.
e.g. if `φ : L.BoundedFormula α 2` represents `P(v₀, v₁, a)`, then
`φ.alls : L.Form α` represents `∀v₀ ∀v₁ P(v₀, v₁, a)`. -/
def alls : ∀ {n}, L.BdForm I n → L.Form I
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula.
e.g. if `φ : L.BoundedFormula α 2` represents `P(v₀, v₁, a)`, then
`φ.exs : L.Form α` represents `∃v₀ ∃v₁ P(v₀, v₁, a)`. -/
def exs : ∀ {n}, L.BdForm I n → L.Form I
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

variable {J : Type u''}

/-- Maps bounded formulas along a map of terms and a map of relations. -/
def mapTermRel {L': Lang} {g : ℕ → ℕ} (fterm : ∀ n, L.Term (I ⊕ Fin n) → L'.Term (J ⊕ (Fin <| g n)))
    (frel : ∀ n, L.Rels n → L'.Rels n)
    (h : ∀ n, L'.BdForm J (g (n + 1)) → L'.BdForm J (g n + 1)) :
    ∀ {n}, L.BdForm I n → L'.BdForm J (g n)
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => equal (fterm _ t₁) (fterm _ t₂)
  | _n, rel R ts => rel (frel _ R) fun i => fterm _ (ts i)
  | _n, imp φ₁ φ₂ => (φ₁.mapTermRel fterm frel h).imp (φ₂.mapTermRel fterm frel h)
  | n, all φ => (h n (φ.mapTermRel fterm frel h)).all

/-- Substitutes the variables in a given formula with terms.
e.g. if `φ = P(v₀, v₁, a)` and we substitute `v₀` with `g(v₂)` and `v₁` with `a`, we get
`φ' = P(g(v₂), a, a)`, that is `(φ.subst f) = P(f(1), f(2), a)` where `f` is defined by
`f(1) = g(v₂)` and `f(2) = a`.-/
def subst {n : ℕ} (φ : L.BdForm I n) (f : I → L.Term I) : L.BdForm I n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : I → J ⊕ (Fin n)) (k : ℕ) : I ⊕ (Fin k) → J ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel {n : ℕ} (g : I → J ⊕ (Fin n)) {k} (φ : L.BdForm I k) : L.BdForm J (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

end BdForm

/-- `&n` is notation for the `n`-th free variable of a bounded formula. -/
scoped[FOL] prefix:arg "?" => FOL.Lang.Term.var ∘ Sum.inr

@[inherit_doc] scoped[FOL] infixl:88 " =' " => FOL.Lang.Term.bdEqual

@[inherit_doc] scoped[FOL] infixr:62 " ⟹ " => FOL.Lang.BdForm.imp

@[inherit_doc] scoped[FOL] prefix:110 "∀'" => FOL.Lang.BdForm.all

@[inherit_doc] scoped[FOL] prefix:arg "∼" => FOL.Lang.BdForm.not

@[inherit_doc] scoped[FOL] infixl:61 " ⇔ " => FOL.Lang.BdForm.iff

@[inherit_doc] scoped[FOL] prefix:110 "∃'" => FOL.Lang.BdForm.ex

namespace Form

variable {J : Type u''}

/-- Relabels a formula's variables along a particular function. -/
def relabel (σ : I → J) : L.Form I → L.Form J :=
  @BdForm.relabel _ _ _ 0 (Sum.inl ∘ σ) 0

/-- The graph of an operation as a first-order formula.
`graph m` represents the formula `y = m x₁ ... xₙ`, where `y` is indexed by `0 : Fin (n + 1)`
-/
def graph (m : L.Ops n) : L.Form (Fin (n + 1)) :=
  Term.equal (var 0) (op m fun i => var i.succ)

end Form

namespace Rels

variable (r : L.Rels 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀' r.bdForm₂ ?0 ?0 -- read this as "for all x, r(x, x)"

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀' ∼(r.bdForm₂ ?0 ?0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀'∀' (r.bdForm₂ ?0 ?1 ⟹ r.bdForm₂ ?1 ?0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀'∀' (r.bdForm₂ ?0 ?1 ⟹ r.bdForm₂ ?1 ?0 ⟹ Term.bdEqual ?0 ?1)

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀'∀'∀' (r.bdForm₂ ?0 ?1 ⟹ r.bdForm₂ ?1 ?2 ⟹ r.bdForm₂ ?0 ?2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀'∀' (r.bdForm₂ ?0 ?1 ⊔ r.bdForm₂ ?1 ?0)

end Rels

namespace BdForm

/-- An atomic formula is either equality or a relation symbol applied to terms.
Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive IsAtomic : L.BdForm I n → Prop
  | equal (t₁ t₂ : L.Term (I ⊕ (Fin n))) : IsAtomic (t₁.bdEqual t₂)
  | rel {m : ℕ} (R : L.Rels m) (ts : Fin m → L.Term (I ⊕ (Fin n))) :
    IsAtomic (R.bdForm ts)

end BdForm


end FOL.Lang
