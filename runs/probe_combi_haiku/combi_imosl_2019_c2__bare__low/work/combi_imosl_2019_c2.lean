import Mathlib

/--
You are given a set of $n$ blocks, each weighing at least 1; their total weight is $2 n$. Prove that for every real number $r$ with $0 \leqslant r \leqslant 2 n-2$ you can choose a subset of the blocks whose total weight is at least $r$ but at most $r+2$.
-/
theorem imosl_2019_c2 (n : ℕ) (blocks : Fin n → ℝ) (h1 : ∀ i, blocks i ≥ 1)
    (h2 : ∑ i, blocks i = 2 * n) :
    ∀ r : ℝ, 0 ≤ r ∧ r ≤ 2 * n - 2 →
      ∃ (s : Finset (Fin n)), (∑ i ∈ s, blocks i) ≥ r ∧ (∑ i ∈ s, blocks i) ≤ r + 2 := by
  -- Case of all weights ≤ 2: add items one at a time.
  have hA : ∀ T : Finset (Fin n), (∀ i ∈ T, blocks i ≤ 2) → ∀ r : ℝ, 0 ≤ r →
      r ≤ ∑ i ∈ T, blocks i →
      ∃ s : Finset (Fin n), s ⊆ T ∧ ∑ i ∈ s, blocks i ≥ r ∧ ∑ i ∈ s, blocks i ≤ r + 2 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ r hr0 hr
      simp at hr
      refine ⟨∅, subset_refl _, ?_, ?_⟩ <;> simp <;> linarith
    | insert a T ha ih =>
      intro hle r hr0 hr
      rw [Finset.sum_insert ha] at hr
      by_cases hr' : r ≤ ∑ i ∈ T, blocks i
      · obtain ⟨s, hs, h⟩ := ih (fun i hi => hle i (Finset.mem_insert_of_mem hi)) r hr0 hr'
        exact ⟨s, hs.trans (Finset.subset_insert _ _), h⟩
      · push_neg at hr'
        refine ⟨insert a T, subset_refl _, ?_, ?_⟩
        · rw [Finset.sum_insert ha]; linarith
        · rw [Finset.sum_insert ha]
          have := hle a (Finset.mem_insert_self _ _)
          linarith
  have hM : ∀ m : ℕ, ∀ T : Finset (Fin n), T.card = m →
      ∑ i ∈ T, blocks i ≤ 2 * (m : ℝ) → ∀ r : ℝ, 0 ≤ r →
      r ≤ ∑ i ∈ T, blocks i - 2 →
      ∃ s : Finset (Fin n), s ⊆ T ∧ ∑ i ∈ s, blocks i ≥ r ∧ ∑ i ∈ s, blocks i ≤ r + 2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro T hT hsum r hr0 hr
    by_cases hbig : ∃ b ∈ T, 2 < blocks b
    · obtain ⟨b, hbT, hb⟩ := hbig
      have hcard := Finset.card_erase_add_one hbT
      have hsE := Finset.add_sum_erase T blocks hbT
      have hk : (T.erase b).card < m := by omega
      have hm : (m : ℝ) = ((T.erase b).card : ℝ) + 1 := by
        rw [← hT, ← hcard]; push_cast; ring
      have hRsum : ∑ i ∈ T.erase b, blocks i ≤ 2 * ((T.erase b).card : ℝ) := by linarith
      have hRge : ((T.erase b).card : ℝ) ≤ ∑ i ∈ T.erase b, blocks i := by
        have := Finset.sum_le_sum (fun i (_ : i ∈ T.erase b) => h1 i)
        simpa using this
      have hbnot : b ∉ T.erase b := by simp
      have hRsub := Finset.erase_subset b T
      by_cases h1' : r ≤ ∑ i ∈ T.erase b, blocks i - 2
      · obtain ⟨s, hs, h⟩ := ih _ hk (T.erase b) rfl hRsum r hr0 h1'
        exact ⟨s, hs.trans hRsub, h⟩
      · push_neg at h1'
        by_cases h2' : blocks b ≤ r
        · obtain ⟨s, hs, h⟩ := ih _ hk (T.erase b) rfl hRsum (r - blocks b) (by linarith)
            (by linarith)
          have hbs : b ∉ s := fun h => hbnot (hs h)
          refine ⟨insert b s, Finset.insert_subset hbT (hs.trans hRsub), ?_, ?_⟩
          · rw [Finset.sum_insert hbs]; obtain ⟨_, _⟩ := h; linarith
          · rw [Finset.sum_insert hbs]; obtain ⟨_, _⟩ := h; linarith
        · push_neg at h2'
          by_cases h3 : blocks b - 2 ≤ r
          · refine ⟨{b}, Finset.singleton_subset_iff.mpr hbT, ?_, ?_⟩
            · rw [Finset.sum_singleton]; linarith
            · rw [Finset.sum_singleton]; linarith
          · push_neg at h3
            by_cases h4 : r ≤ ∑ i ∈ T.erase b, blocks i
            · refine ⟨T.erase b, hRsub, ?_, ?_⟩ <;> linarith
            · push_neg at h4
              exfalso
              have hT' : ∑ i ∈ T, blocks i = blocks b + ∑ i ∈ T.erase b, blocks i := by
                linarith
              linarith
    · push_neg at hbig
      exact hA T hbig r hr0 (by linarith)
  intro r hr
  obtain ⟨s, _, h⟩ := hM n Finset.univ (by simp) (by rw [h2]) r hr.1
    (by rw [h2]; linarith [hr.2])
  exact ⟨s, h⟩
