import CompLean.PrimRec.Definitions.Prelim
import Mathlib.Tactic

open Nat

-- Fun Theorems

theorem curryFun_uncurryFun {A B C : Type} (f : A → B → C) :
    curryFun (uncurryFun f) = f := by
  rfl

theorem uncurryFun_curryFun {A B C : Type} (f : A × B → C) :
    uncurryFun (curryFun f) = f := by
  rfl

theorem prodFun_diagFun_eq_pairFun {Z A B : Type} {α : Z → A} {β : Z → B} :
    prodFun α β ∘ diagFun Z = pairFun α β := by
  rfl

theorem constFun_eq_curryFun {A B : Type} (b : B) : constFun A b = curryFun (π₁ B A) b := by
  rfl

def curry_uncurryEquiv (A B C : Type) : (A × B → C) ≃ (A → B → C) where
  toFun := curryFun
  invFun := uncurryFun
  left_inv := uncurryFun_curryFun
  right_inv := curryFun_uncurryFun

-- Vec Theorems

/-- An explicit bijection between singletons and the underlying type. -/
def singletonsEquivSelf (A : Type) : A^[1] ≃ A where
  toFun := singletonToSelf
  invFun := selfToSingleton
  left_inv v := by
    simp [singletonToSelf]
    unfold selfToSingleton
    funext x
    fin_cases x
    simp
  right_inv a := by
    rfl

/-- An explicit bijection between the type of tuples of length `2` and the type of pairs. -/
def pairsEquivBinaryProd (A : Type) : A^[2] ≃ A × A where
  toFun := tupleToProd A
  invFun := prodToTuple A
  left_inv v := by
    funext x
    simp [tupleToProd, prodToTuple]
    fin_cases x
    · simp
    · simp
  right_inv p := by
    ext
    all_goals
    dsimp [prodToTuple, prodToTuple]
    rfl

def triplesEquivTernaryProd (A : Type) : A^[3] ≃ A × A × A where
  toFun := tripleToProd A
  invFun := prodToTriple A
  left_inv v := by
    funext x
    simp [tripleToProd, prodToTriple]
    fin_cases x
    · simp
    · simp
    · simp
  right_inv p := by
    ext
    all_goals
    dsimp [tripleToProd, prodToTriple]

def precomposeOfEquiv {A B : Type} (e : A ≃ B) (C : Type) : (A → C) ≃ (B → C) :=
  Equiv.piCongrLeft' (fun _ ↦ C) e


def foo : (A^[2] → B) ≃ (A → A → B) :=
  let f := curry_uncurryEquiv A A B
  let g : ((Fin 2 → A) → B) ≃ (A × A → B) := precomposeOfEquiv (pairsEquivBinaryProd A) B
  g.trans f
