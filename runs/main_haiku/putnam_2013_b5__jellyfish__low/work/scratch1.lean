import Mathlib
open Function Set
example (n : ℕ) (k : Set.Icc 1 n) : True := by
  have : ({f : (Set.Icc 1 n → Set.Icc 1 n) | True}).encard = k * n ^ (n - 1) := by
    sorry
  trivial
