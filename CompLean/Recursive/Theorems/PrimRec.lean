import CompLean.Recursive.Definitions.PrimRec
import Mathlib.Tactic

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
  | succ => exact hg _

theorem vec_fun_id {n} : VecFun n n id := fun i => Prim.proj i

theorem comp_vec_fun {p n f g} (g_prim : Prim n g) (f_prim : VecFun p n f) : Prim p (g ∘ f) :=
  (g_prim.comp _ f_prim).of_eq fun v => by
  unfold π
  rfl

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
  unfold pred' π
  induction v 0 <;> rfl

theorem neg : Prim 1 neg' := by
  have g : Prim 0 _ := Prim.const 1
  have h : Prim 2 _ := Prim.const 0
  have f := Prim.prec g h
  refine of_eq f ?_
  unfold neg'
  intro p
  induction p 0 <;> aesop

theorem sgn : Prim 1 sgn' := sorry

theorem add : Prim 2 add' := by
  have g : Prim 1 (fun v => v 0) := Prim.proj 0
  have h : Prim 3 (fun v => v 1 + 1) := comp₁ Nat.succ Prim.succ (Prim.proj 1)
  have f := Prim.prec g h
  refine of_eq f ?_
  unfold add'
  intro p
  induction p 0 with
  | zero => abel
  | succ => simp_all; abel

theorem mul : Prim 2 mul' := by
  have g : Prim 1 (fun v => 0) := Prim.const 0
  have h : Prim 3 (fun v => v 1 + v 2) := comp₂' (fun x y => x + y) Prim.add (Prim.proj 1) (Prim.proj 2)
  have f := Prim.prec g h
  refine of_eq f ?_
  unfold mul'
  intro p
  induction p 0 with
  | zero => noncomm_ring
  | succ => simp_all; noncomm_ring

theorem factorial : Prim 1 factorial' := by
  have g : Prim 0 _ := Prim.const 1
  have h : Prim 2 _ := comp₂' _ Prim.mul (comp₁ _ Prim.succ (Prim.proj 0)) (Prim.proj 1)
  have f := Prim.prec g h
  refine of_eq f ?_
  unfold factorial'
  intro p
  induction p 0 <;> aesop

theorem sub : Prim 2 sub' := by
  have g : Prim 1 (fun v => v 0) := Prim.proj 0
  have h : Prim 3 (fun v => v 1 - 1) := comp₁ Nat.pred Prim.pred (Prim.proj 1)
  have f := comp_vec_fun (Prim.prec g h) ((Prim.proj 1).cons ((Prim.proj (0 : Fin 2)).cons Prim.nil))
  refine of_eq f ?_
  unfold π
  simp [sub']
  intro p
  induction p 1 with
  | zero => rfl
  | succ => grind

theorem max : Prim 2 max' := by
  -- max(x, y) = add(x, sub(y, x))
  have f : Prim 2 (fun v => Nat.add (v 0) (Nat.sub (v 1) (v 0))) :=
    comp₂' Nat.add Prim.add (Prim.proj 0) (comp₂' Nat.sub Prim.sub (Prim.proj 1) (Prim.proj 0))
  refine of_eq f ?_
  grind [max']

theorem min : Prim 2 min' := by
  -- min(x, y) = sub(x, sub(x, y))
  have f : Prim 2 (fun v => Nat.sub (v 0) (Nat.sub (v 0) (v 1))) :=
    comp₂' Nat.sub Prim.sub (Prim.proj 0) (comp₂' Nat.sub Prim.sub (Prim.proj 0) (Prim.proj 1))
  refine of_eq f ?_
  grind [min']

theorem dist : Prim 2 dist' := by
  -- dist(x, y) = add(sub(x, y), sub(y, x))
  have f : Prim 2 (fun v => Nat.add (Nat.sub (v 0) (v 1)) (Nat.sub (v 1) (v 0))) :=
    comp₂' Nat.add Prim.add (comp₂' Nat.sub Prim.sub (Prim.proj 0) (Prim.proj 1)) (comp₂' Nat.sub Prim.sub (Prim.proj 1) (Prim.proj 0))
  refine of_eq f ?_
  grind [dist']

theorem eq : Prim 2 eq' := sorry

theorem pow : Prim 2 pow' := sorry

end Prim
