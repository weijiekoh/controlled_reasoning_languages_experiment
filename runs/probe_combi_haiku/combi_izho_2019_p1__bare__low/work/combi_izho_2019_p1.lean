import Mathlib

open Nat

/--
Prove that there are at least 100! ways to partition the number 100! into summands from the set $\{1!, 2!, 3!, \ldots, 99!\}$. (Partitions differing in the order of summands are considered the same; any summand can be taken multiple times. We remind that $n!=1 \cdot 2 \cdot \ldots \cdot n$.)
-/
theorem izho_2019_p1 : ((@Finset.univ 100!.Partition).filter
    (fun p => ∀ i ∈ p.parts, ∃ k ∈ Finset.Icc 1 99, i = Nat.factorial k)).card ≥ 100! := by
  have h4 : 4 ∣ 100! := Nat.dvd_factorial (by norm_num) (by norm_num)
  have h36 : 36 ≤ 100! := le_trans (by norm_num) (Nat.self_le_factorial 100)
  generalize 100! = N at h4 h36 ⊢
  obtain ⟨m, rfl⟩ := h4
  let f : ℕ × ℕ → Nat.Partition (4 * m) := fun p =>
    if h : 2 * p.1 + 6 * p.2 ≤ 4 * m then
      ⟨Multiset.replicate p.1 2 + Multiset.replicate p.2 6 +
        Multiset.replicate (4 * m - (2 * p.1 + 6 * p.2)) 1,
        by
          intro i hi
          simp only [Multiset.mem_add, Multiset.mem_replicate] at hi
          omega,
        by
          simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
          omega⟩
    else
      ⟨{4 * m}, by
          intro i hi
          simp at hi
          omega,
        by simp⟩
  have hs : (Finset.range m ×ˢ Finset.range 4).card = 4 * m := by
    simp [Finset.card_product]; ring
  rw [ge_iff_le]
  suffices h : (Finset.range m ×ˢ Finset.range 4).card ≤ _ by rw [hs] at h; exact h
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
    have hb : 2 * p.1 + 6 * p.2 ≤ 4 * m := by omega
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [f, dif_pos hb]
    intro i hi
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hi
    rcases hi with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact ⟨2, by simp, by decide⟩
    · exact ⟨3, by simp, by decide⟩
    · exact ⟨1, by simp, by decide⟩
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hq
    have hb : 2 * p.1 + 6 * p.2 ≤ 4 * m := by omega
    have hb' : 2 * q.1 + 6 * q.2 ≤ 4 * m := by omega
    simp only [f, dif_pos hb, dif_pos hb'] at hpq
    have hp' := congrArg Nat.Partition.parts hpq
    have c2 := congrArg (Multiset.count 2) hp'
    have c6 := congrArg (Multiset.count 6) hp'
    simp [Multiset.count_replicate] at c2 c6
    exact Prod.ext c2 c6
