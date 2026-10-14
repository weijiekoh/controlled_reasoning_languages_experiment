import Mathlib
open Nat
#check @Nat.card_divisors_le_self
example (n:ℕ): n.divisors.card ≤ 2*Nat.sqrt n := by exact?
