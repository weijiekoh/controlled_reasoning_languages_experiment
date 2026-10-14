import Mathlib

/--
Use the pigeonhole principle to prove that a graph of order n ≥ 2 always has two vertices of the same degree.
-/
theorem brualdi_ch11_5 (n : ℕ) (h_n: n ≥ 2) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ v1 v2, v1 ≠ v2 ∧ G.degree v1 = G.degree v2 := by
  by_contra hc
  push_neg at hc
  have key : ∀ (t : Finset ℕ), t.card < n → (∀ v, G.degree v ∈ t) → False := by
    intro t ht hm
    obtain ⟨a, _, b, _, hab, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin n))) (t := t) (by simpa using ht) (f := fun v => G.degree v) (by intro v _; exact hm v)
    exact hc a b hab h
  by_cases h0 : ∃ u, G.degree u = 0
  · obtain ⟨u, hu⟩ := h0
    apply key (Finset.range (n-1)) (by simp; omega)
    intro v
    simp only [Finset.mem_range]
    by_cases hv : v = u
    · subst hv; omega
    · have hsub : G.neighborFinset v ⊆ (Finset.univ \ {v, u}) := by
        intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and, not_or]
        refine ⟨G.ne_of_adj hw |>.symm, ?_⟩
        rintro rfl
        have : v ∈ G.neighborFinset w := by simpa using hw.symm
        have := Finset.card_pos.mpr ⟨v, this⟩
        rw [SimpleGraph.card_neighborFinset_eq_degree] at this
        omega
      have := Finset.card_le_card hsub
      rw [Finset.card_univ_diff, Finset.card_pair hv] at this
      simp at this
      omega
  · push_neg at h0
    apply key (Finset.Icc 1 (n-1)) (by simp; omega)
    intro v
    have := G.degree_lt_card_verts v
    simp at this
    simp only [Finset.mem_Icc]
    have := h0 v
    omega
