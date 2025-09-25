import CompLean.FOL.Definitions.Term

/-! ## Bounded Formula and Formula in First-Order Logic

`BoundedFormula` is a type that represents first-order logic formulas with a specific variable structure.
This should not be confused with bounded quantifier appearing for instance in `Δ₀` formulas in arithmetic hierarchy. Instead, here "bounded" refers to the way bound variables are handled in the formulas using a modified version of de Bruijn variables.

More specifically, `L.BoundedFormula α n` represents a formula where:
- `α` indexes "free variables" that cannot be quantified over
- `n` (a natural number) represents the number of additional variables indexed by `Fin n` that **can** be quantified over

## The Structure

From the inductive definition, a `BoundedFormula α n` can be:
1. `falsum` - the false formula (⊥)
2. `equal t₁ t₂` - equality between two terms
3. `rel R ts` - a relation applied to terms
4. `imp f₁ f₂` - implication between formulas
5. `all f` - universal quantification (∀)

## Examples in First-Order Logic

Let me give some concrete examples:

### Example 1: Simple Formula
Consider the formula `∀x. P(x)` in standard notation.
- This would be represented as `BoundedFormula Empty 0`
- The `x` is handled internally using the de Bruijn index system
- Since we're quantifying over all variables, `n = 0` (no unquantified Fin-indexed variables remain)

### Example 2: Formula with Free Variables
Consider `P(a) ∧ ∀x. Q(x, a)` where `a` is a free variable.
- This might be `BoundedFormula α 0` where `α` contains the index for `a`
- The `a` stays free (indexed by `α`), while `x` gets bound by the quantifier

### Example 3: Partially Quantified Formula
Consider a formula `P(x, y)` where we want to later quantify over `x` but keep `y` free.
- This could be `BoundedFormula α 1` where:
  - `α` indexes `y` (the variable that stays free)
  - The `1` indicates there's one variable (indexed by `Fin 1`) that could be quantified over
  - To get `∀x. P(x, y)`, you'd apply the `all` constructor

### Example 4: The Quantification Process
The comment explains: "For any `φ : L.BoundedFormula α (n + 1)`, we define the formula `∀' φ : L.BoundedFormula α n` by universally quantifying over the variable indexed by `n : Fin (n + 1)`."

So if you have:
- `φ : BoundedFormula α 2` representing something like `P(x₀, x₁, a)`
- `∀' φ : BoundedFormula α 1` represents `∀x₁. P(x₀, x₁, a)`
- `∀' (∀' φ) : BoundedFormula α 0` represents `∀x₀. ∀x₁. P(x₀, x₁, a)`

## Why This Design?

This approach allows for:
1. **Systematic handling of variable binding** without name clashes
2. **Type-safe quantification** - you can only quantify over variables that are available
3. **Compositional formula construction** - you can build complex formulas step by step
4. **Clear separation** between free variables (that come from outside context) and bound variables (that are introduced by quantifiers)

The system is particularly useful for formal verification and automated theorem proving, where you need precise control over variable scoping and binding.
-/


universe u v w u' v'

namespace FOL.Language

variable (L : Language.{u, v}) {I : Type u'}

/-- `BoundedFormula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (I ⊕ (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Rels l) (ts : Fin l → L.Term (I ⊕ (Fin n))) : BoundedFormula n
  /-- The implication between two bounded formulas -/
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  /-- The universal quantifier over bounded formulas -/
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n



end FOL.Language
