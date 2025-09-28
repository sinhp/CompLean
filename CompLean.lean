-- This module serves as the root of the `CompLean` library.
-- Import modules here that should be built as part of the library.
import CompLean.FOL.Definitions.Formula
import CompLean.FOL.Definitions.Language
import CompLean.FOL.Definitions.Structure
import CompLean.FOL.Definitions.Term
import CompLean.FOL.Definitions.Theory
import CompLean.FOL.Examples.Peano
import CompLean.FOL.Examples.etc
-- fails with: "environment already contains 'ack._unary' from Mathlib.Computability.Ackermann"
-- import CompLean.Recursive.Definitions.Ackermann
import CompLean.Recursive.Definitions.Prelim
import CompLean.Recursive.Definitions.PrimRec
import CompLean.Recursive.Theorems.Prelim
import CompLean.Recursive.Theorems.PrimRec
