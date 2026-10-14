import Mathlib

lemma lemA {ι : Type*} [DecidableEq ι] (f : ι → ℝ) : ∀ (s : Finset ι), (∀ i ∈ s, f i ≤ 2) → ∀ r : ℝ, 0 ≤ r → r ≤ ∑ i ∈ s, f i → ∃ t ⊆ s, r ≤ ∑ i ∈ t, f i ∧ ∑ i ∈ t, f i ≤ r + 2 := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ r h0 h1
    simp at h1
    exact ⟨∅, by simp, by simp; linarith, by simp; linarith⟩
  | insert a s ha ih =>
    intro hf r h0 h1
    rw [Finset.sum_insert ha] at h1
    by_cases h : r ≤ ∑ i ∈ s, f i
    · obtain ⟨t, ht, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) r h0 h
      exact ⟨t, ht.trans (Finset.subset_insert _ _), h3⟩
    · have := hf a (Finset.mem_insert_self _ _)
      refine ⟨insert a s, subset_rfl, ?_, ?_⟩
      · rw [Finset.sum_insert ha]; exact h1
      · rw [Finset.sum_insert ha]; linarith

lemma lemB {ι : Type*} [DecidableEq ι] (f : ι → ℝ) : ∀ (n : ℕ) (s : Finset ι), s.card = n → (∀ i ∈ s, 1 ≤ f i) → ∑ i ∈ s, f i ≤ 2 * n → ∀ r : ℝ, 0 ≤ r → r ≤ ∑ i ∈ s, f i - 2 → ∃ t ⊆ s, r ≤ ∑ i ∈ t, f i ∧ ∑ i ∈ t, f i ≤ r + 2 := by
  intro n
  induction n with
  | zero =>
    intro s hs _ hW r h0 h1
    rw [Finset.card_eq_zero] at hs
    subst hs
    simp at h1
    linarith
  | succ n ih =>
    intro s hs h1 hW r h0 hr
    have hne : s.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s f hne
    by_cases hb : f m ≤ 2
    · exact lemA f s (fun i hi => (hmax i hi).trans hb) r h0 (by linarith)
    · push_neg at hb
      have hsum : ∑ i ∈ s, f i = f m + ∑ i ∈ s.erase m, f i := by
        rw [Finset.add_sum_erase _ _ hm]
      have hc : (s.erase m).card = n := by
        rw [Finset.card_erase_of_mem hm]; omega
      have h1' : ∀ i ∈ s.erase m, 1 ≤ f i := fun i hi => h1 i (Finset.mem_of_mem_erase hi)
      have hRn : (n:ℝ) ≤ ∑ i ∈ s.erase m, f i := by
        have := Finset.card_nsmul_le_sum (s.erase m) f 1 h1'
        rw [hc] at this; simpa using this
      have hW' : ∑ i ∈ s.erase m, f i ≤ 2 * (n:ℝ) := by
        push_cast at hW; linarith
      by_cases hc1 : r ≤ ∑ i ∈ s.erase m, f i - 2
      · obtain ⟨t, ht, h3⟩ := ih _ hc h1' hW' r h0 hc1
        exact ⟨t, ht.trans (Finset.erase_subset _ _), h3⟩
      · push_neg at hc1
        by_cases hc2 : r ≤ ∑ i ∈ s.erase m, f i
        · exact ⟨s.erase m, Finset.erase_subset _ _, hc2, by linarith⟩
        · push_neg at hc2
          by_cases hc3 : r < f m
          · refine ⟨{m}, by simpa using hm, by simp; linarith, by simp; push_cast at hW; linarith⟩
          · push_neg at hc3
            obtain ⟨t, ht, h3, h4⟩ := ih _ hc h1' hW' (r - f m) (by linarith) (by linarith)
            have hmt : m ∉ t := fun h => by simpa using ht h
            refine ⟨insert m t, ?_, ?_, ?_⟩
            · intro x hx
              rcases Finset.mem_insert.1 hx with rfl | hx
              · exact hm
              · exact Finset.mem_of_mem_erase (ht hx)
            · rw [Finset.sum_insert hmt]; linarith
            · rw [Finset.sum_insert hmt]; linarith


/--
You are given a set of $n$ blocks, each weighing at least 1; their total weight is $2 n$. Prove that for every real number $r$ with $0 \leqslant r \leqslant 2 n-2$ you can choose a subset of the blocks whose total weight is at least $r$ but at most $r+2$.
-/
theorem imosl_2019_c2 (n : ℕ) (blocks : Fin n → ℝ) (h1 : ∀ i, blocks i ≥ 1)
    (h2 : ∑ i, blocks i = 2 * n) :
    ∀ r : ℝ, 0 ≤ r ∧ r ≤ 2 * n - 2 →
      ∃ (s : Finset (Fin n)), (∑ i ∈ s, blocks i) ≥ r ∧ (∑ i ∈ s, blocks i) ≤ r + 2 := by
  intro r ⟨h0, hr⟩
  obtain ⟨t, -, h⟩ := lemB blocks n Finset.univ (by simp) (fun i _ => h1 i) (by rw [h2]) r h0 (by rw [h2]; exact hr)
  exact ⟨t, h⟩
