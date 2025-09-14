/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import CompLean.Recursive.Definitions.Prelim

open Vector Nat List

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
      Prim n g → (∀ i, Prim p (f i)) → Prim p (fun (x : ℕ^[p]) ↦ g (fun (i : Fin n) ↦ f i x))
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

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def VecFun (p n) (f : ℕ^[p] → ℕ^[n]) : Prop :=
  ∀ i, Prim p (fun x => π i (f x))

end Prim
