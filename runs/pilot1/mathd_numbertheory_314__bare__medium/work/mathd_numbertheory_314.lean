import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_314
  (r n : ℕ)
  (h₀ : r = 1342 % 13)
  (h₁ : 0 < n)
  (h₂ : 1342∣n)
  (h₃ : n % 13 < r) :
  6710 ≤ n := by
  subst h₀
  obtain ⟨k, rfl⟩ := h₂
  by_contra h
  have hk : k < 5 := by omega
  have hk0 : 0 < k := by omega
  interval_cases k <;> omega