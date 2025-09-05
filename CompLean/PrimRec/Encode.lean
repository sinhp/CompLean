import Mathlib.Data.Nat.Notation


@[pp_nodot]
def pair (a b : ℕ) : ℕ :=
  if a < b then b * b + a else a * a + a + b


/-- Pairing function for the natural numbers. -/
@[pp_nodot]
def pair' (a b : ℕ) : ℕ :=
  if b < a then a * a + b else b * b + b + a


#eval pair 0 0
#eval pair 0 1
#eval pair 1 0


#eval pair' 0 0
#eval pair' 1 0
#eval pair' 0 1
#eval pair' 3 0
#eval pair' 3 3
