import Mathlib
open Polynomial
example (p : ℕ) (a : ℕ → ZMod p) (haother : ∀ k : Set.Icc 1 (p - 1), a k = ((k : ℕ) ^ ((p - 1) / 2)) % p) (k : Set.Icc 1 (p-1)): False := by
  have := haother k
  set_option pp.all true in trace_state
  sorry
