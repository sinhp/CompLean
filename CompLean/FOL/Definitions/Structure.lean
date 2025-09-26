import CompLean.FOL.Definitions.Term
import Mathlib.Data.Fin.VecNotation
--import Mathlib -- why do we need this? -- gives weird errors otherwise


namespace FOL.Lang

/-- A first-order __structure__ on a type `M`, considered as the base (aka underlying set) of the strucuture, consists of interpretations of all
the symbols in a given language. Each operation of arity `n` is interpreted as a function sending tuples of length `n` to `M`, and
a relation of arity `n` a set of the tuples of length `n`.  -/
@[ext]
class Structure (L : Lang.{u,v}) (M : Type w) where
  /-- Interpretation of the operation symbols -/
  opMap : ∀ {n}, L.Ops n → (tuple n M) → M := by
    exact fun {n} => isEmptyElim -- if there is no function symbols of arity `n`, return nothing by default.
  /-- Interpretation of the relation symbols -/
  relMap : ∀ {n}, L.Rels n → Set (tuple n M) := by
    exact fun {n} => isEmptyElim -- if there is no relation symbols of arity `n`, return nothing by default.

variable (L : Lang.{u,v})

variable (M : Type w) (N : Type w') [L.Structure M] [L.Structure N]

open Structure

variable {M} {I : Type u'}

/-- A term `t` with variables indexed by `I` can be evaluated by giving a value to each variable. -/
def Term.realize (v : I → M) : ∀ _t : L.Term I, M
  | var k => v k
  | op m ts => opMap m fun i => (ts i).realize v

open Structure

def Inhabited.trivialStructure [Inhabited M] : L.Structure M :=
  ⟨default, default⟩

variable (M)

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of Operations and maps tuples in one structure where a given relation is sati to
  tuples in the second structure where that relation is still true. -/
structure Hom where
  /-- The underlying function of a homomorphism of structures -/
  toFun : M → N
  /-- The homomorphism commutes with the interpretations of the function symbols -/
  map_op' : ∀ {n} (f : L.Ops n) (x), toFun (opMap f x) = opMap f (toFun ∘ x) := by
    intros; trivial
  /-- The homomorphism sends related elements to related elements -/
  map_rel' : ∀ {n} (r : L.Rels n) (x), relMap r x → relMap r (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FOL] notation:25 A " →[" L "] " B => FOL.Lang.Hom L A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} (f : L.Ops n) (x), toFun (opMap f x) = opMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Rels n) (x), relMap r (toFun ∘ x) ↔ relMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FOL] notation:25 A " ↪[" L "] " B => FOL.Lang.Embedding L A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} (f : L.Ops n) (x), toFun (opMap f x) = opMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Rels n) (x), relMap r (toFun ∘ x) ↔ relMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FOL] notation:25 A " ≃[" L "] " B => FOL.Lang.Equiv L A B

variable {N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

/-- Interpretation of a constant symbol -/
@[coe]
def constantMap (c : L.Constants) : M := opMap c (default : tuple 0 M)

-- instance : CoeTC L.Constants M :=
--   ⟨constantMap⟩

end FOL.Lang
