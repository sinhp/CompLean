/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fin.Tuple.Basic

open Nat

/-!
# Functions
-/

/-- Type of functions from `A` to `B`. -/
abbrev Function (A B : Type) := A → B

#check (succ : ℕ → ℕ)

def compFun {A B C : Type} (f : B → C) (g : A → B) : A → C :=
  fun a => f (g a)

def idNat : ℕ → ℕ := id

def succTwice : ℕ → ℕ := compFun succ succ

#eval succTwice 3

/-!
## Binary cartesian product and projections
-/

def π₁ (A B : Type) : A × B → A := fun p => p.1

def π₂ (A B : Type) : A × B → B := fun p => p.2

/-- pairing of two functions. -/
def pairFun {A B Z : Type} (α : Z → A) (β : Z → B) : Z → A × B := fun z => (α z, β z)

def prodFun {A B C D : Type} (f : A → C) (g : B → D) : A × B → C × D := Prod.map f g

#eval (1, [5,6,7]).map (· + 1) (List.length)

def diagFun (A : Type) : A → A × A := fun a => (a, a)

/-- Frege-Schönfinkel-Curry transformation. -/
def curryFun {A B C : Type} : (A × B → C) → A → B → C := fun f a b => f (a, b)

/-- Inverse of the Frege-Schönfinkel-Curry transformation. -/
def uncurryFun {A B C : Type} : (A → B → C) → A × B → C := fun f p => f p.1 p.2

def constFun {B : Type} (A : Type) (b : B) : A → B := fun _ => b

/-!
## n-fold projections
-/

/-- The type of n-tuples of elements of `A`. -/
notation A "^[" n "]" => Fin n → A

/-- The constant n-tuple with all entries equal to `a`, i.e. `(a, a, ..., a)`. -/
def constVec {A : Type} {n : ℕ} (a : A) : A^[n] := fun _ => a

/-- The empty tuple. -/
def emptyVec (A : Type) : A^[0] := fun x => x.elim0

def headOfVec {A : Type} {n : ℕ} (v : A^[n+1]) : A := v 0

def tailOfVec {A : Type} {n : ℕ} (v : A^[n+1]) : A^[n] := fun i => v (i.succ)

/-- The i-th projection from an n-tuple to its i-th entry, i.e. `(a_0, a_1, ..., a_(n-1)) ↦ a_i`. -/
def π {A : Type} {n : ℕ} (i : Fin n) : A^[n] → A := fun v => v i

def emptyTupleToUnit {A : Type} : A^[0] → PUnit := fun _ => PUnit.unit

def unitToEmptyTuple {A : Type} : PUnit → A^[0] := fun _ => fun x => x.elim0

def emptyTuple : A^[0] := fun x => x.elim0

def singletonToSelf {A : Type} : A^[1] → A := fun v => v 0

def selfToSingleton {A : Type} : A → A^[1] := fun a => fun _ => a

notation "≪" a "≫" => selfToSingleton a

#check ≪5≫


def tupleToProd (A : Type) : A^[2] → A × A := fun v => (v 0, v 1)

def prodToTuple (A : Type) : A × A → A^[2] := fun p => fun i => if i = 0 then p.1 else p.2

def tripleToProd (A : Type) : A^[3] → A × A × A :=
  fun v => (v 0, (v 1, v 2))

def prodToTriple (A : Type) : A × A × A → A^[3] := fun p => fun i =>
  match i with
  | ⟨0, _⟩ => p.1
  | ⟨1, _⟩ => p.2.1
  | ⟨2, _⟩ => p.2.2

@[inherit_doc]
infixr:67 " <:> " => Fin.cons

/-- Construct an (n+1)-tuple from an element and an n-tuple, i.e.
`consVec a (a_0, a_1, ..., a_(n-1)) = (a, a_0, a_1, ..., a_(n-1))`. -/
def consVec {A : Type} {n : ℕ} (a : A) (v : A^[n]) : A^[n+1] := a <:> v

def uncurry₂ : (ℕ → ℕ → ℕ) → (ℕ^[2] → ℕ) := fun f v => f (v 0) (v 1)

namespace Nat

def add' : ℕ^[2] → ℕ := fun v => v 0 + v 1

def mul' : ℕ^[2] → ℕ := fun v => v 0 * v 1

def pred' : ℕ^[1] → ℕ := fun v => v 0 - 1

def sub' : ℕ^[2] → ℕ := fun v => v 0 - v 1

def max' : ℕ^[2] → ℕ := fun v => max (v 0) (v 1)

def min' : ℕ^[2] → ℕ := fun v => min (v 0) (v 1)

end Nat

#eval pred' (selfToSingleton 1)

#eval sub' (consVec 5 (selfToSingleton 3))

#eval max' (consVec 5 (selfToSingleton 4))
