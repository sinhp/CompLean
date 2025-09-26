import CompLean.FOL.Definitions.Formula

namespace FOL.Lang

variable (L : Lang.{u, v})

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence

end FOL.Lang
