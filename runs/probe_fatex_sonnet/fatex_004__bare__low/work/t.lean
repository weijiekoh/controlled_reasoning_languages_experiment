import Mathlib
open MulAction
example (p : ℕ) (h_odd : Odd p) (G : Type)
    (hp : p.Prime) [Finite G] [Group G] (h_card : Nat.card G = p * (p + 1))
    (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal) : ∃ (n : ℕ), p + 1 = 2 ^ n := by
  classical
  have := Fact.mk hp
  have hnd : ¬ p ∣ p + 1 := by
    intro h; have := (Nat.dvd_add_right (dvd_refl p)).1 h; exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hPcard : ∀ P : Sylow p G, Nat.card P = p := by
    intro P
    rw [P.card_eq_multiplicity, h_card, Nat.factorization_mul hp.ne_zero (by omega),
      Finsupp.add_apply, hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hnd]
    simp
  have hn : Nat.card (Sylow p G) = p + 1 := by
    obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
    have h1 := card_sylow_modEq_one p G
    have h2 : Nat.card (Sylow p G) ∣ p + 1 := by
      have := P.card_dvd_index
      have h5 := (P : Subgroup G).card_mul_index
      rw [hPcard P, h_card] at h5
      have h6 := Nat.eq_of_mul_eq_mul_left hp.pos h5
      rwa [← h6]
    have h3 : Nat.card (Sylow p G) ≠ 1 := by
      intro h
      have : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.1 h).1
      exact h_sylow P (Sylow.normal_of_subsingleton P)
    have h4 := Nat.le_of_dvd (by omega) h2
    have h6 : Nat.card (Sylow p G) % p = 1 := by
      have := h1; unfold Nat.ModEq at this; rw [Nat.mod_eq_of_lt hp.one_lt] at this; exact this
    have h7 := Nat.div_add_mod (Nat.card (Sylow p G)) p
    have h8 : Nat.card (Sylow p G) / p ≤ 1 := by
      by_contra hk1
      have : p * 2 ≤ p * (Nat.card (Sylow p G) / p) := Nat.mul_le_mul_left _ (by omega)
      have := hp.two_le
      omega
    generalize Nat.card (Sylow p G) / p = k at *
    interval_cases k <;> omega
  have hN : ∀ P : Sylow p G, Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = p := by
    intro P
    have h3 : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = p + 1 := by
      rw [← hn]; exact P.card_eq_index_normalizer.symm
    have h2 := (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_mul_index
    rw [h3, h_card] at h2
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  have hcomm : ∀ x z : G, orderOf z = p → Commute x z → x ∈ Subgroup.zpowers z := by
    intro x z hz hc
    have hKc : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
    have hK : IsPGroup p (Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by rw [hKc]; simp)
    obtain ⟨P, hP⟩ := hK.exists_le_sylow
    have hKP : Subgroup.zpowers z = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hP (by rw [hKc, hPcard P])
    have hz' : x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff, ← hKP]
      intro h
      constructor
      · rintro ⟨n, rfl⟩
        rw [(hc.zpow_right n).mul_inv_cancel]; exact ⟨n, rfl⟩
      · intro hh
        obtain ⟨n, hn⟩ := hh
        have hn' : x * h * x⁻¹ = z ^ n := hn.symm
        have e1 : h = x⁻¹ * (z ^ n) * x := by rw [← hn']; group
        have e : x⁻¹ * z ^ n * x = z ^ n := by
          simpa using ((hc.zpow_right n).inv_left).mul_inv_cancel
        rw [e1, e]; exact ⟨n, rfl⟩
    have : Subgroup.normalizer ((P : Subgroup G) : Set G) = (P : Subgroup G) :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.le_normalizer) (by rw [hN P, hPcard P])).symm
    rw [hKP, ← this]; exact hz'
  have := Fintype.ofFinite G
  have hcl : ∀ q : ℕ, q.Prime → q ∣ p + 1 → ∃ S : Finset G, (∀ g ∈ S, orderOf g = q) ∧ p ≤ S.card := by
    intro q hq hqd
    have := Fact.mk hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) q
      (by rw [h_card]; exact Dvd.dvd.mul_left hqd p)
    refine ⟨(orbit (ConjAct G) x).toFinset, ?_, ?_⟩
    · intro g hg
      rw [Set.mem_toFinset] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [← hx]
      show orderOf (c • x) = _
      rw [ConjAct.smul_def]
      simpa using MulEquiv.orderOf_eq (MulAut.conj (ConjAct.ofConjAct c)) x
    · rw [Set.toFinset_card]
      have h1 := card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
      have hcg : Fintype.card (ConjAct G) = p * (p + 1) := by
        rw [← h_card, Nat.card_eq_fintype_card]
        exact Fintype.card_congr ConjAct.ofConjAct.toEquiv
      rw [hcg] at h1
      have hs : Fintype.card (stabilizer (ConjAct G) x) ∣ p + 1 := by
        have hd : Fintype.card (stabilizer (ConjAct G) x) ∣ p * (p + 1) := by
          rw [← hcg]; rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
          exact Subgroup.card_subgroup_dvd_card _
        have hcop : Nat.Coprime (Fintype.card (stabilizer (ConjAct G) x)) p := by
          rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          intro hpd
          obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer (ConjAct G) x) p
            (by rw [Nat.card_eq_fintype_card]; exact hpd)
          have hw1 : orderOf (ConjAct.ofConjAct (w : ConjAct G)) = p := by
            rw [MulEquiv.orderOf_eq ConjAct.ofConjAct (w : ConjAct G), Subgroup.orderOf_coe, hw]
          have hw2 := w.2
          rw [mem_stabilizer_iff, ConjAct.smul_def] at hw2
          have hc : Commute x (ConjAct.ofConjAct (w : ConjAct G)) := by
            rw [mul_inv_eq_iff_eq_mul] at hw2
            exact hw2.symm
          have hm := hcomm x _ hw1 hc
          have h3 := Subgroup.orderOf_dvd_natCard _ hm
          rw [Nat.card_zpowers, hw1, hx] at h3
          have := (Nat.prime_dvd_prime_iff_eq hq hp).1 h3
          subst this
          exact hnd hqd
        exact hcop.dvd_of_dvd_mul_left hd
      have h2 := Nat.le_of_dvd (by omega) hs
      by_contra hlt
      push Not at hlt
      have : Fintype.card (orbit (ConjAct G) x) * Fintype.card (stabilizer (ConjAct G) x) < p * (p+1) := by
        calc _ < p * Fintype.card (stabilizer (ConjAct G) x) := by
              apply Nat.mul_lt_mul_of_pos_right hlt
              exact Fintype.card_pos
          _ ≤ _ := Nat.mul_le_mul_left _ h2
      omega
  sorry
