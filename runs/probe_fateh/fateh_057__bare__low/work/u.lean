import Mathlib
open Polynomial
example {F : Type} [Field F] (p : ℕ) [ExpChar F p] (hs : Function.Surjective (frobenius F p)) : PerfectField F := by exact?
example {F : Type} [Field F] (S : IntermediateField F F) (h : S = ⊥) : True := by
  have := (IntermediateField.eq_bot_iff)
  trivial
