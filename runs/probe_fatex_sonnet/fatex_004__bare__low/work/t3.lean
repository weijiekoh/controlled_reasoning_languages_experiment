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
  have hord : ∀ (P : Sylow p G) (g : G), g ∈ (P : Subgroup G) → g ≠ 1 → orderOf g = p := by
    intro P g hg hg1
    apply orderOf_eq_prime _ hg1
    have := pow_card_eq_one' (G := (P : Subgroup G)) (x := ⟨g, hg⟩)
    rw [hPcard P] at this
    exact congrArg Subtype.val this
  have hzp : ∀ (P : Sylow p G) (g : G), g ∈ (P : Subgroup G) → g ≠ 1 → Subgroup.zpowers g = (P : Subgroup G) := by
    intro P g hg hg1
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hg)
    rw [Nat.card_zpowers, hord P g hg hg1, hPcard P]
  have hA : (p + 1) * (p - 1) ≤ (Finset.univ.filter (fun g : G => orderOf g = p)).card := by
    have := Fintype.ofFinite (Sylow p G)
    let T : Finset (Σ _ : Sylow p G, G) :=
      Finset.univ.sigma (fun P => ((P : Subgroup G) : Set G).toFinset.erase 1)
    have hT : T.card = (p + 1) * (p - 1) := by
      rw [Finset.card_sigma]
      have : ∀ P ∈ (Finset.univ : Finset (Sylow p G)),
          (((P : Subgroup G) : Set G).toFinset.erase 1).card = p - 1 := by
        intro P _
        have h' : Fintype.card ((P : Subgroup G) : Set G) = p := by
          rw [← Nat.card_eq_fintype_card]; exact hPcard P
        rw [Finset.card_erase_of_mem (by simp), Set.toFinset_card, h']
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hn]
      simp
    rw [← hT]
    apply Finset.card_le_card_of_injOn (fun s => s.2)
    · rintro ⟨P, g⟩ hs
      simp only [T, Finset.mem_coe, Finset.mem_sigma, Finset.mem_erase, Set.mem_toFinset,
        SetLike.mem_coe] at hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hord P g hs.2.2 hs.2.1
    · rintro ⟨P, g⟩ hs ⟨P', g'⟩ hs' h
      simp only [T, Finset.mem_coe, Finset.mem_sigma, Finset.mem_erase, Set.mem_toFinset,
        SetLike.mem_coe] at hs hs'
      simp only at h
      subst h
      have : P = P' := by
        apply Sylow.ext
        rw [← hzp P g hs.2.2 hs.2.1, ← hzp P' g hs'.2.2 hs'.2.1]
      subst this; rfl
  obtain ⟨S2, hS2, hS2c⟩ := hcl 2 Nat.prime_two (by obtain ⟨k, hk⟩ := h_odd; exact ⟨k + 1, by omega⟩)
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (p + 1) with h | ⟨q, hq, hqd, hqo⟩
  · exact h
  exfalso
  obtain ⟨Sq, hSq, hSqc⟩ := hcl q hq hqd
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd h_odd (by decide)
  have hq2 : q ≠ 2 := by rintro rfl; exact absurd hqo (by decide)
  have hqp : q ≠ p := by rintro rfl; exact hnd hqd
  set A := Finset.univ.filter (fun g : G => orderOf g = p) with hAdef
  have d1 : Disjoint A S2 := by
    rw [Finset.disjoint_left]; intro g hg hg2
    rw [hAdef, Finset.mem_filter] at hg; have := hS2 g hg2; omega
  have d2 : Disjoint (A ∪ S2) Sq := by
    rw [Finset.disjoint_left]; intro g hg hg2
    have := hSq g hg2
    rcases Finset.mem_union.1 hg with h | h
    · rw [hAdef, Finset.mem_filter] at h; omega
    · have := hS2 g h; omega
  have d3 : Disjoint (A ∪ S2 ∪ Sq) {1} := by
    rw [Finset.disjoint_left]; intro g hg hg2
    rw [Finset.mem_singleton] at hg2; subst hg2
    rcases Finset.mem_union.1 hg with h | h
    · rcases Finset.mem_union.1 h with h | h
      · rw [hAdef, Finset.mem_filter] at h; simp at h; exact hp.one_lt.ne' h.symm
      · have := hS2 _ h; simp at this
    · have := hSq _ h; simp at this; exact hq.one_lt.ne' this.symm
  have hle := Finset.card_le_univ (A ∪ S2 ∪ Sq ∪ {1})
  rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1, Finset.card_singleton, Fintype.card_eq_nat_card, h_card] at hle
  have hp3 := hp.two_le
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  rw [hm] at hA hle hS2c hSqc
  simp only [Nat.add_sub_cancel] at hA
  nlinarith
