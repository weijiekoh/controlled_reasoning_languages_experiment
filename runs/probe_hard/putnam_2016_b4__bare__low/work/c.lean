import Mathlib
example (n : ℕ) (hn : 0 < n) : (Multiset.replicate n 2).lcm ∣ 2 := by
  apply Multiset.lcm_dvd.mpr
  intro b hb; rw [Multiset.eq_of_mem_replicate hb]
example (n : ℕ) (hn : 1≤ n): (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2*n)) => σ.cycleType = Multiset.replicate n 2)).card
      * (2 ^ n * n.factorial) = (2 * n).factorial := by
  have := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2*n)) (Multiset.replicate n 2)
  have h2 : (Multiset.replicate n 2).toFinset = {2} := by
    rw [Multiset.toFinset_replicate]; simp; omega
  simp [h2] at this
  trace_state
  sorry
