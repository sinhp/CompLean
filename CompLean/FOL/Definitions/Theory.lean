import CompLean.FOL.Definitions.Formula

namespace FOL.Language

variable (L : Language.{u, v})

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence




end FOL.Language
