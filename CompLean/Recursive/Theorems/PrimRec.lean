import CompLean.Recursive.Definitions.PrimRec
import Mathlib.Tactic.Basic

namespace Prim

open Nat

theorem of_eq {p} {f g : ℕ^[p] → ℕ} (hf : Prim p f) (H : ∀ i, f i = g i) :
    Prim p g :=
  (funext H : f = g) ▸ hf

/-- Every constant function `ℕ^[p] → ℕ` is primitive recursive. -/
theorem const {k} : ∀ (m : ℕ), Prim k (constFun _ m)
  | 0 => zero.comp Fin.elim0 (fun i => i.elim0)
  | m + 1 => succ.comp _ fun _ => const m

protected theorem nil {n} : VecFun n 0 (fun _ => emptyTuple) := fun i => i.elim0

protected theorem cons {n m f g} (hf : Prim n f) (hg : VecFun n m g) :
    VecFun n (m + 1) (fun v => (f v) <:> (g v)) := by
  intro i
  cases i using Fin.cases with
  | zero => assumption
  | succ x => exact hg ⟨x, x.isLt⟩

theorem vec_fun_id {n} : VecFun n n id := fun i => Prim.proj i

theorem comp_vec_fun {p n f g} (g_prim : Prim n g) (f_prim : VecFun p n f) : Prim p (g ∘ f) :=
  (g_prim.comp _ f_prim).of_eq fun v => by simp [π]

/-- The compostion of a primitive recursive `f : ℕ^[p] → ℕ` with a primitive recursive vector function
`g : ℕ → ℕ` is primitive recursive. -/
theorem comp₁ (g : ℕ → ℕ) (g_prim : Prim 1 fun x => g (x 0)) {p f} (hf : Prim p f) :
    Prim p (fun x => g (f x)) :=
  g_prim.comp _ fun _ => hf

theorem comp₂ (g : ℕ → ℕ → ℕ) (g_prim : Prim 2 fun x => g (x 0) (x 1)) {p f}
    (f_prim : Prim p f) : Prim p fun x => g (f x) (f x) := by
  exact g_prim.comp _ fun _ => f_prim

theorem comp₂' (g : ℕ → ℕ → ℕ) (g_prim : Prim 2 fun x => g (x 0) (x 1)) {p f h}
    (f_prim : Prim p f) (h_prim : Prim p h) : Prim p (fun x => g (f x) (h x)) := by
  refine g_prim.comp (fun (i : Fin 2) x => Fin.cases (f x) ≪h x≫  i) ?_
  intro i
  cases i using Fin.cases <;> assumption

theorem prec' {n f g h} (f_prim : Prim n f) (g_prim : Prim n g) (h_prim : Prim (n + 2) h) :
    Prim n fun v => (f v).rec (g v) fun y IH : ℕ => h (y <:> IH <:> v) := by
  simpa using comp_vec_fun (prec g_prim h_prim) (f_prim.cons vec_fun_id)

theorem pred : Prim 1 pred' :=
  (prec' (proj 0) (const 0) (proj 0)).of_eq fun v => by
  simp [pred', π]
  induction v 0 with
  | zero => rfl
  | succ => rfl

theorem add : Prim 2 add' := by
  have g : Prim 1 (fun x => x 0) := Prim.proj 0
  have h : Prim 3 (fun v => Nat.succ (v 1)) := comp₁ Nat.succ Prim.succ (Prim.proj 1)
  have f := Prim.prec g h
  refine of_eq f ?_
  simp only [Fin.tail]
  have r (x y : ℕ) : Nat.rec x (fun _ z => Nat.succ z) y = x + y := by
    induction y with
    | zero => simp
    | succ _ _ => grind
  simp [add']
  intro i
  simp_all [Nat.add_comm]

theorem mul : Prim 2 mul' := by
  have g : Prim 1 (fun _ => 0) := Prim.const 0
  have h : Prim 3 (fun v => v 1 + v 2) := comp₂' (fun x y => x + y) Prim.add (Prim.proj 1) (Prim.proj 2)
  have f := Prim.prec g h
  refine of_eq f ?_
  have r (x y : ℕ) : Nat.rec 0 (fun _ z => z + y) x = x * y := by
    induction x with
    | zero => simp
    | succ _ _ => grind
  aesop -- if using `aesop` is overkill: `intro i; simp; apply r`

theorem sub : Prim 2 sub' := by
  sorry

theorem max : Prim 2 max' := by
  sorry

theorem min : Prim 2 min' := by
  sorry

end Prim
