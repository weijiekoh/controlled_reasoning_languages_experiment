
theorem putnam_2011_a6_aux
(G : Type*) [CommGroup G] [Fintype G]
(n : ℕ)
(gset : Set G)
(k : ℕ)
(mgprob : ℕ → G → ℝ)
(hmgprob : mgprob = (fun (m : ℕ) (x : G) => ({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℝ) / k ^ m))
(hn : n = (Fintype.elems : Finset G).card)
(hk : gset.encard = k)
(hgsetprop : k < n)
(hgset1 : 1 ∈ gset)
(hgsetgen : Subgroup.closure gset = ⊤)
: ∃ b ∈ Set.Ioo (0 : ℝ) 1, ∃ C > 0, Tendsto (fun m : ℕ => (1 / b ^ (2 * m)) * (∑ x : G, (mgprob m x - 1 / n) ^ 2)) atTop (𝓝 C) := by
  classical
  subst hmgprob
  have hfin : gset.Finite := Set.finite_of_encard_eq_coe hk
  haveI : Fintype gset := hfin.fintype
  have hkn : gset.ncard = k := by
    have h2 := hfin.cast_ncard_eq
    rw [hk] at h2
    exact_mod_cast h2
  have hcard : Fintype.card gset = k := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hkn]
  have hkpos : 0 < Fintype.card gset := Fintype.card_pos_iff.mpr ⟨⟨1, hgset1⟩⟩
  have hnN : n = Fintype.card G := by rw [hn]; exact Finset.card_univ
  have hnR : (n : ℝ) = (Fintype.card G : ℝ) := by rw [hnN]
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  -- counting
  have hcnt : ∀ (m : ℕ) (x : G), ({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℝ)
      = ((Finset.univ.filter (fun f : Fin m → gset =>
          ∑ i, Additive.ofMul ((f i).1 : G) = Additive.ofMul x)).card : ℝ) := by
    intro m x
    congr 1
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    congr 1
    trace_state
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ofMul_prod]
    exact ⟨fun h => by rw [h], fun h => Equiv.injective _ h⟩
  sorry

