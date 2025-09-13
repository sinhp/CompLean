/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import CompLean.Recursive.Definitions.Prelim

open Vector Nat List

@[inherit_doc]
local infixr:67 " <:> " => Fin.cons

def append {A : Type} {n : ℕ} (a : A) (v : A^[n]) : A^[n + 1] := a <:> v

inductive Prim : (p : ℕ) → Set (ℕ^[p] → ℕ)
  /-- The costant zero function `0 : 1 → ℕ` is Primitive recursive. -/
  | zero : Prim 0 (fun _ ↦ 0)
  /-- The successor function `succ : ℕ → ℕ` is Primitive recursive. -/
  | succ : Prim 1 (fun v ↦ succ (v 0))
  /-- The projections `π i` are Primitive recursive. -/
  | proj {p} (i : Fin p) : Prim p (π i)
  /-- If `f` is Primitive recursive function of arity `n` and and `g0, ..., g(n-1)` are Primitive recursive,
  then the composition `f(g0, ..., g(n-1))` is Primitive recursive. -/
  | comp {p n} {g : ℕ^[n] → ℕ} (f : Fin n → ℕ^[p] → ℕ) :
      Prim n g → (∀ i, Prim p (f i)) → Prim p (fun x ↦ g (fun i ↦ f i x))
  /-- If `f` is a Primitive recursive function of arity `n` and `g` is a Primitive recursive function of
  arity `n + 2`, then the function `h` defined by Primitive recursion from `f` and `g` is Primitive recursive.
  That is, the function `h : ℕ^[n + 1] → ℕ` defined by
  ```
    f(0, x₁, ..., xₚ) = g(x₁, ..., xₚ)
    f(succ(y), x₁, ..., xₚ) = h(y, f(y, x₁, ..., xₚ), x₁, ..., xₚ)
  ```
  is Primitive recursive. -/
  | prec {p g h} :
      Prim p g →
        Prim (p + 2) h →
          Prim (p + 1) (fun x : ℕ^[p + 1] ↦
            Nat.rec (g (Fin.tail x)) (fun y IH ↦ h (y <:> IH <:> Fin.tail x)) (x 0))

namespace Prim

theorem of_eq {p} {f g : ℕ^[p] → ℕ} (hf : Prim p f) (H : ∀ i, f i = g i) :
    Prim p g :=
  (funext H : f = g) ▸ hf

/-- Every constant function `ℕ^[p] → ℕ` is primitive recursive. -/
theorem const {k} : ∀ (m : ℕ), Prim k (constFun _ m)
  | 0 => zero.comp Fin.elim0 (fun i => i.elim0)
  | m + 1 => succ.comp _ fun _ => const m

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def VecFun (p n) (f : ℕ^[p] → ℕ^[n]) : Prop :=
  ∀ i, Prim p (fun x => π i (f x))

protected theorem nil {n} : VecFun n 0 (fun _ => emptyTuple) := fun i => i.elim0

protected theorem cons {n m f g} (hf : Prim n f) (hg : VecFun n m g) :
    VecFun n (m + 1) (fun v => (f v) <:> (g v)) := by
  intro i
  sorry

theorem vec_fun_id {n} : VecFun n n id := fun i => Prim.proj i

theorem comp_vec_fun {p n f g} (g_prim : Prim n g) (f_prim : VecFun p n f) : Prim p (g ∘ f) :=
  (g_prim.comp _ f_prim).of_eq fun v => by simp [π]

/-- The compostion of a primitive recursive `f : ℕ^[p] → ℕ` with a primitive recursive vector function
`g : ℕ → ℕ` is primitive recursive. -/
theorem comp₁ (g : ℕ → ℕ) (hg : Prim 1 fun x => g (x 0)) {p f} (hf : Prim p f) :
    Prim p (fun x => g (f x)) :=
  hg.comp _ fun _ => hf

theorem comp₂ (g : ℕ → ℕ → ℕ) (hg : Prim 2 fun x => g (x 0) (x 1)) {n f}
    (hf : Prim n f) : Prim n fun x => g (f x) (f x) := by
  exact hg.comp _ fun _ => hf

theorem prec' {n f g h} (f_prim : Prim n f) (g_prim : Prim n g) (h_prim : Prim (n + 2) h) :
    Prim n fun v => (f v).rec (g v) fun y IH : ℕ => h (y <:> IH <:> v) := by
  simpa using comp_vec_fun (prec g_prim h_prim) (f_prim.cons vec_fun_id)

theorem pred : Prim 1 fun v => (v 0).pred :=
  (prec' (proj 0) (const 0) (proj 0)).of_eq fun v => by simp; sorry

theorem add : Prim 2 fun x => x 0 + x 1 := by
  have g : Prim 1 (fun x => x 0) := Prim.proj 0
  have h : Prim 3 (fun v => Nat.succ (v 1)) := comp₁ Nat.succ Prim.succ (Prim.proj 1)
  have f := Prim.prec g h
  refine of_eq f ?_
  simp [Fin.tail] -- non-terminal simp, consider using "simp only [...]"
  have r (x y : ℕ) : Nat.rec x (fun _ z => Nat.succ z) y = x + y := by
    induction y with
    | zero => simp
    | succ _ _ => grind
  grind

theorem comp₂' (f : ℕ → ℕ → ℕ) (hf : Prim 2 fun v => f (v 0) (v 1)) {n g h}
    (hg : Prim n g) (hh : Prim n h) : Prim n fun v => f (g v) (h v) := by
  refine hf.comp (fun i v => Fin.cases (g v) (fun _ => h v) i) ?_
  intro i
  cases i using Fin.cases <;> assumption

theorem mul : Prim 2 fun x => x 0 * x 1 := by
  have g : Prim 1 (fun _ => 0) := Prim.const 0
  have h : Prim 3 (fun v => v 1 + v 2) := comp₂' (fun x y => x + y) Prim.add (Prim.proj 1) (Prim.proj 2)
  have f := Prim.prec g h
  refine of_eq f ?_
  have r (x y : ℕ) : Nat.rec 0 (fun _ z => z + y) x = x * y := by
    induction x with
    | zero => simp
    | succ _ _ => grind
  aesop -- if using `aesop` is overkill: `intro i; simp; apply r`

end Prim
