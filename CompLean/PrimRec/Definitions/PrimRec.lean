import CompLean.PrimRec.Definitions.Prelim

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
  | comp {p n} {f : ℕ^[n] → ℕ} (g : Fin n → ℕ^[p] → ℕ) :
      Prim n f → (∀ i, Prim p (g i)) → Prim p (fun x ↦ f (fun i ↦ g i x))
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
            Nat.rec (g (Fin.tail x)) (fun y IH ↦ h (Fin.cons y (Fin.cons IH (Fin.tail x)))) (x 0))

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

theorem vec_fun_id {n} : VecFun n n id := fun i => Prim.proj i

theorem comp_vec_fun {p n f g} (g_prim : Prim n g) (f_prim : VecFun p n f) : Prim p (g ∘ f) :=
  (g_prim.comp _ f_prim).of_eq fun v => by simp [π]

theorem comp₁ (g : ℕ → ℕ) (hg : Prim 1 fun x => g (x 0)) {p f} (hf : Prim p f) :
    Prim p (fun x => g (f x)) :=
  hg.comp _ fun _ => hf

theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : Prim 2 fun v => f (v 0) (v 1)) {n g h}
    (hg : Prim n g) (hh : Prim n h) : Prim n fun v => f (g v) (h v) := by
  sorry

theorem add : Prim 2 fun x => x 0 + x 1 := by
  sorry

theorem mul : Prim 2 fun x => x 0 * x 1 := by
  sorry

end Prim
