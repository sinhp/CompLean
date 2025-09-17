import CompLean.FOL.Definitions.Basic

import Mathlib

universe u v

namespace FOL.Language

/-- The inductive type of operation symbols for the language of monoids.
It contains the operations (*, 1). -/
inductive MonoidOps : Arity → Type u
  | mul : MonoidOps 2
  | one : MonoidOps 0
  deriving DecidableEq

inductive AddMonoidOps : Arity → Type u
  | add : AddMonoidOps 2
  | zero : AddMonoidOps 0
  deriving DecidableEq

/-- The inductive type of operation symbols for the language of groups.
It contains the operations (*, 1, ⁻¹). -/
inductive GroupOps : Arity → Type u
  | mul : GroupOps 2
  | inv : GroupOps 1
  | one : GroupOps 0
  deriving DecidableEq

inductive AddGroupOps : Arity → Type u
  | add : AddGroupOps 2
  | neg : AddGroupOps 1
  | zero : AddGroupOps 0
  deriving DecidableEq

/-- The inductive type of operation symbols for the language of rings.
It contains the operations (+, *, -, 0, 1). -/
inductive RingOps : Arity → Type u
  | add : RingOps 2
  | mul : RingOps 2
  | neg : RingOps 1
  | zero : RingOps 0
  | one : RingOps 0
  deriving DecidableEq

inductive SemiringModuleOp (R : Type u) : Arity → Type u
  | add : SemiringModuleOp R 2
  | neg : SemiringModuleOp R 1
  | zero : SemiringModuleOp R 0
  | smul (r : R) : SemiringModuleOp R 1
  deriving DecidableEq

scoped notation "∅" => fun _ => PEmpty

/-- The language of monoids contains the operations (*, 1) and no relation. -/
def monoid : Language where
  Ops := MonoidOps
  Rels := fun _ => Empty
  deriving IsAlgebraic

/-- The language of additive monoids contains the operations (+, 0) and no relation. -/
def addMonoid : Language.{u,v} where
  Ops := AddMonoidOps
  Rels := ∅
  deriving IsAlgebraic

/-- The language of groups contains the operations (*, 1, ⁻¹) and no relation. -/
def group : Language where
  Ops := GroupOps
  Rels := ∅
  deriving IsAlgebraic

def addGroup : Language where
  Ops := AddGroupOps
  Rels := ∅
  deriving IsAlgebraic

/-- The language of rings contains the operations (+,*,-,0,1) and no relation. -/
def ring : Language where
  Ops := RingOps
  Rels := ∅
  deriving IsAlgebraic

private def neg : ring.Ops 1 := RingOps.neg
#check (Sum.inl ⟨1, neg⟩: ring.Symbols)

private def mul : ring.Ops 2 := RingOps.mul

private def add : ring.Ops 2 := RingOps.add

/-
**Note**: The language of `semiringModule R` is uniquely determined by the semiring `R`.
This suggests we should think of an algebraic theory as a kind of generalized semiring/ring and the models of algebraic theories as generalized modules over these semirings/rings.
-/

set_option trace.Meta.isDefEq true in
/-- The language of semiring modules over a semiring `R` contains the operations (+, 0, -, r • x) for every `r : R` and no relation. -/
def semiringModule (R : Type u) : Language where
  Ops := SemiringModuleOp R
  Rels := ∅
  --deriving IsAlgebraic -- note: this is not working!
  -- the issue might be that it tries to derive IsAlgebraic (fun R _ => SemiringModule R)
  -- This is a "def deriving", and the way it works is that it uses the value of the definition to try to synthesize an instance. There's no deriving handler except for processDefDeriving.
  -- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60deriving.20IsAlgebraic.60.20not.20working/with/533473926

instance (R : Type u) : IsAlgebraic (semiringModule R) := by
  unfold semiringModule; infer_instance

inductive preorderRel : Arity → Type
  | le : preorderRel 2

def preorder : Language where
  Ops := fun _ => Empty
  Rels := preorderRel
  deriving IsRelational

inductive preOrderWithTopRel : Arity → Type
  | le : preOrderWithTopRel 2
  | top : preOrderWithTopRel 0

def preOrderWithTop : Language where
  Ops := fun _ => Empty
  Rels := preOrderWithTopRel
  deriving IsRelational

/-- The type of relations for the language of graphs, consisting of a single binary relation `adj`. -/
inductive graphRel : ℕ → Type
  | adj : graphRel 2
  deriving DecidableEq

/-- The language consisting of a single relation representing adjacency. -/
def graph : Language where
  Ops := fun _ => Empty
  Rels := graphRel
  deriving IsRelational

/-- The symbol representing the adjacency relation. -/
abbrev adj : graph.Rels 2 := .adj

@[instance]
def addMonoidStrOfNatAdd : addMonoid.Structure ℕ where
  opMap
    | .add => (fun p => p 1 + p 2)
    | .zero => (fun _ => 0)

def monoidStrOfNatMul : monoid.Structure ℕ where
  opMap
    | .mul => (fun p => p 1 * p 2)
    | .one => (fun _ => 1)

/-- The monoid structure on lists, where the `add` operation is concatenation of lists and the `zero` operation is the empty list. -/
@[instance]
def addMonoidStrOfListAppend (α : Type*) : addMonoid.Structure (List α) where
  opMap
    | .add => (fun l => List.append (l 1) (l 2))
    | .zero => (fun _ => [])

/--
Alternately selects elements from two input list, starting with the first element of the first list, followed by the first element of the second list, then the second element of the first list, and so on, until all elements from both lists are exhausted. If one list is longer than the other, the remaining elements of the longer list are appended to the end of the resulting list.
-/
protected def _root_.List.interleave {α : Type*} : List α → List α → List α
  | [], l2 => l2
  | a::as, l2 => a :: List.interleave l2 as
termination_by l1 l2 => l1.length + l2.length

#check List.insert

/-- The additive monoid structure on lists, where the `add` operation is interleaving and the `zero` operation is the empty list. -/
def addMonoidStrOfListInterleave (α : Type*) : addMonoid.Structure (List α) where
  opMap
    | .add => (fun l => List.interleave (l 1) (l 2))
    | .zero => (fun _ => [])

/-- The additive monoid structure on lists, where the `add` operation is merging (using le as a switch) and the `zero` operation is the empty list. -/
def monoidStrOfListMerge (α : Type*) (le : α → α → Bool := by exact fun a b => a ≤ b) :
    monoid.Structure (List α) where
  opMap
    | .mul => (fun l => List.merge (l 1) (l 2) le)
    | .one => (fun _ => [])

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
def graphStrOfSimpleGraph {V : Type*} (G : SimpleGraph V) : Language.graph.Structure V where
  relMap | .adj => (fun x => G.Adj (x 0) (x 1))

/-- The monoid structure homomorphism from list monoid (with append operation) to natural
numbers monoid (with addition operation), where the underlying Option of the homomorphism is
the length of the list. -/
def monoidStrHomOfNatList (α : Type*) : addMonoid.Hom (List α) ℕ where
  toFun := List.length
  map_op' {n}
    | .add => (fun x => List.length_append (x 1) (x 2))
    | .zero => (fun _ => List.length_nil)

section

/-- A type ι of three variables. -/
private inductive XYZ
  | x : XYZ
  | y : XYZ
  | z : XYZ
  deriving DecidableEq

#check ring.Term

private def zero : ring.Constants := RingOps.zero
private def one : ring.Constants := RingOps.one

local notation "#0" => zero.term (L:= ring)
local notation "#1"  => one.term (L:= ring)
local notation "#x" => Term.var XYZ.x
local notation "#y" => Term.var XYZ.y
local notation "#z" => Term.var XYZ.z

local infixl:51 " + " => RingOps.add.apply₂
local infixl:52 " * " => RingOps.mul.apply₂

#check #0
#check #1
#check #x
#check op add ![#0, #1]
#check op add ![#x, #y]
#check op mul ![op add ![#1, op neg ![#x]], op add ![#1, #y]]

#check #x + #y
#check #x + #0
-- #check #x * #y + #1 -- note: seems bracketing is needed.
-- #check #x * #y + #z
#check (#x * #y) + #1
-- #check -#x
#check (#1 + (op neg ![#x])) * (#1 + #y)


end


end Language
end FOL
