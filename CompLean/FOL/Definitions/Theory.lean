import CompLean.FOL.Definitions.Formula

import Mathlib

universe u v u' v' w w'

namespace FOL.Lang

open Finset

variable (L : Lang.{u, v}) (I : Type u') [DecidableEq I]

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence

/-- Given a valuation v, a nat `n`, and an `x : S`, return `v` truncated to its first n values, with the rest of the values replaced by x. --/
def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
if k < n then v k else x

notation v "[" x " // " n "]" => subst_realize v x n

#check insert

#synth Insert ℕ (Set ℕ)

#synth Insert ℕ (Finset ℕ)


#synth Insert I (Finset I)

variable (i : I) (s : Finset I) (f : I → β)

#check f '' s

#check Finset.image


#check insert i s

instance : DecidableEq (L.Form I) := sorry


-- inductive Der : Finset (L.Form I) → L.Form I → Type u
-- | axm     {Γ A} (h : A ∈ Γ) : Der Γ A
-- | impI    {Γ : Finset (L.Form I)} (A : (L.Form I)) {B : L.Form I} (h : Der (insert A Γ) B) : Der Γ (A ⟹ B)
-- | impE    {Γ} (A) {B} (h₁ : Der Γ (A ⟹ B)) (h₂ : Der Γ A) : Der Γ B
-- | falsumE {Γ : Finset (L.Form I)} {A} (h : Der (insert ∼A Γ) ⊥) : Der Γ A
-- | allI    {Γ A} (h : Der (image lift_formula1 Γ) A) : Der Γ (∀' A)
-- | allE₂   {Γ} A t (h : Der Γ (∀' A)) : Der Γ (A[t // 0])
-- | ref     (Γ t) : Der Γ (t ≃ t)
-- | subst₂  {Γ} (s t f) (h₁ : Der Γ (s ≃ t)) (h₂ : Der Γ (f[s // 0])) : Der Γ (f[t // 0])





end FOL.Lang
