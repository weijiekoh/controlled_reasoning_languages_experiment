import Mathlib

/--
Use the pigeonhole principle to prove that a graph of order n ≥ 2 always has two vertices of the same degree.
-/
theorem brualdi_ch11_5 (n : ℕ) (h_n: n ≥ 2) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ v1 v2, v1 ≠ v2 ∧ G.degree v1 = G.degree v2 := by
  by_contra h
  push_neg at h
  have hlt : ∀ v : Fin n, G.degree v < n := by
    intro v
    have := G.degree_lt_card_verts v
    simpa using this
  let f : Fin n → Fin n := fun v => ⟨G.degree v, hlt v⟩
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    apply h a b hne
    have := congrArg Fin.val hab
    simpa [f] using this
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  obtain ⟨u, hu⟩ := hsurj ⟨0, by omega⟩
  obtain ⟨v, hv⟩ := hsurj ⟨n - 1, by omega⟩
  have hu0 : G.degree u = 0 := by
    have := congrArg Fin.val hu
    simpa [f] using this
  have hv1 : G.degree v = n - 1 := by
    have := congrArg Fin.val hv
    simpa [f] using this
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact (G.ne_of_adj hw).symm
  have hcard : (Finset.univ.erase v).card ≤ (G.neighborFinset v).card := by
    rw [G.card_neighborFinset_eq_degree, hv1, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have huv : u ≠ v := by
    intro huv
    subst huv
    omega
  have hmem : u ∈ G.neighborFinset v := by
    rw [heq]
    simp [huv]
  rw [SimpleGraph.mem_neighborFinset] at hmem
  have hpos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, hmem.symm⟩
  omega
