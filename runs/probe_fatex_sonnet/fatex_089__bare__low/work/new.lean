import Mathlib

namespace Problem89

/--
Prove that if $\#G = 336$ then $G$ is not simple.
-/
theorem not_isSimpleGroup_of_card_eq_336 (G : Type) [Group G]
    [Finite G] (h_card : Nat.card G = 336) : ¬ IsSimpleGroup G := by
  intro hS
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hcardP : ∀ P : Sylow 7 G, Nat.card P = 7 := by
    intro P
    rw [Sylow.card_eq_multiplicity, h_card]
    have : (336:ℕ) = 7 * 48 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    have h48 : (48:ℕ).factorization 7 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h48, Nat.Prime.factorization_self (by norm_num : Nat.Prime 7)]
  have hbot : ∀ P : Sylow 7 G, ¬ (P : Subgroup G).Normal := by
    intro P hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) hn with h | h
    · have := hcardP P; rw [h, Subgroup.card_bot] at this; omega
    · have := hcardP P; rw [h, Subgroup.card_top, h_card] at this; omega
  obtain ⟨P0⟩ : Nonempty (Sylow 7 G) := inferInstance
  classical
  haveI : Fintype (Sylow 7 G) := Fintype.ofFinite _
  have hidx : (P0 : Subgroup G).index = 48 := by
    have := Subgroup.card_mul_index (P0 : Subgroup G)
    rw [hcardP, h_card] at this; omega
  have hX : Nat.card (Sylow 7 G) = 8 := by
    have h1 := card_sylow_modEq_one 7 G
    have h2 := Sylow.card_dvd_index P0
    rw [hidx] at h2
    have h3 : Nat.card (Sylow 7 G) ≤ 48 := Nat.le_of_dvd (by norm_num) h2
    have hne1 : Nat.card (Sylow 7 G) ≠ 1 := by
      intro h
      haveI : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.1 h).1
      exact hbot P0 (Sylow.normal_of_subsingleton P0)
    unfold Nat.ModEq at h1
    generalize Nat.card (Sylow 7 G) = n at *
    interval_cases n <;> omega
  have hpr : ∀ (H : Subgroup G) (P : Sylow 7 G), H ≤ P → H ≠ ⊥ → H = P := by
    intro H P hle hne
    have hd : Nat.card H ∣ 7 := hcardP P ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hd) with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq H h) hne
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, h])
  have hA : ∀ h : G, h ∈ (P0 : Subgroup G) → ∀ R : Sylow 7 G, R ≠ P0 → h • R = R → h = 1 := by
    intro h hh R hR hfix
    by_contra hne
    have hle : Subgroup.zpowers h ≤ P0 := (Subgroup.zpowers_le).2 hh
    have hH : IsPGroup 7 (Subgroup.zpowers h) := IsPGroup.to_le P0.isPGroup' hle
    have hne' : Subgroup.zpowers h ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hne
    have hfp : R ∈ MulAction.fixedPoints (Subgroup.zpowers h) (Sylow 7 G) := by
      intro m
      have : Subgroup.zpowers h ≤ MulAction.stabilizer G R := (Subgroup.zpowers_le).2 (MulAction.mem_stabilizer_iff.2 hfix)
      exact MulAction.mem_stabilizer_iff.1 (this m.2)
    have h2 := (IsPGroup.sylow_mem_fixedPoints_iff hH).1 hfp
    have e1 := hpr _ P0 hle hne'
    have e2 := hpr _ R h2 hne'
    exact hR (Sylow.ext (e2.symm.trans e1))
  have hY : Nat.card {x : Sylow 7 G // x ≠ P0} = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, hX]
  have hfix0 : ∀ g : G, g ∈ (P0 : Subgroup G) → g • P0 = P0 := fun g hg =>
    Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hg)
  have hT : ∀ R R' : Sylow 7 G, R ≠ P0 → R' ≠ P0 → ∃ g ∈ (P0 : Subgroup G), g • R = R' := by
    intro R R' hR hR'
    have hne : ∀ g : ↥(P0 : Subgroup G), (g:G) • R ≠ P0 := by
      intro g hg
      apply hR
      calc R = (g:G)⁻¹ • ((g:G) • R) := by rw [inv_smul_smul]
        _ = P0 := by rw [hg]; exact hfix0 _ (inv_mem g.2)
    let f : ↥(P0 : Subgroup G) → {x : Sylow 7 G // x ≠ P0} := fun g => ⟨(g:G) • R, hne g⟩
    have hf : Function.Injective f := by
      intro g g' hgg
      have h1 : (g:G) • R = (g':G) • R := congrArg Subtype.val hgg
      have h2 : ((g:G)⁻¹ * g') • R = R := by
        rw [mul_smul, ← h1, inv_smul_smul]
      have h3 := hA _ (mul_mem (inv_mem g.2) g'.2) R hR h2
      have : (g:G) = g' := by simpa [inv_mul_eq_one] using h3
      exact Subtype.ext this
    have hb := hf.bijective_of_nat_card_le (by rw [hY, hcardP])
    obtain ⟨g, hg⟩ := hb.2 ⟨R', hR'⟩
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  let φ := MulAction.toPermHom G (Sylow 7 G)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker inferInstance with h | h
    · exact h
    · exfalso; apply hbot P0
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      apply Sylow.smul_eq_iff_mem_normalizer.1
      have : g ∈ φ.ker := h ▸ Subgroup.mem_top g
      exact congrArg (fun p => p P0) this
  have hsign : ∀ g, Equiv.Perm.sign (φ g) = 1 := by
    have hn : ((Equiv.Perm.sign : Equiv.Perm (Sylow 7 G) →* ℤˣ).comp φ).ker.Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hn with h | h
    · exfalso
      have hi : Function.Injective ((Equiv.Perm.sign : Equiv.Perm (Sylow 7 G) →* ℤˣ).comp φ) := (MonoidHom.ker_eq_bot_iff _).1 h
      have h1 := Nat.card_le_card_of_injective _ hi
      rw [h_card] at h1
      have : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; exact Fintype.card_units_int
      omega
    · intro g
      have : g ∈ ((Equiv.Perm.sign : Equiv.Perm (Sylow 7 G) →* ℤˣ).comp φ).ker := h ▸ Subgroup.mem_top g
      exact this
  have hN : Nat.card (Subgroup.normalizer ((P0 : Subgroup G) : Set G)) = 42 := by
    have := Subgroup.card_mul_index (Subgroup.normalizer ((P0 : Subgroup G) : Set G))
    have e : Nat.card (Sylow 7 G) = (Subgroup.normalizer ((P0 : Subgroup G) : Set G)).index := Sylow.card_eq_index_normalizer P0
    rw [← e, hX, h_card] at this; omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.normalizer ((P0 : Subgroup G) : Set G)) 2 (by rw [hN]; norm_num)
  set t : G := (x : G) with htdef
  have ht : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe]; exact hx
  have htP : t • P0 = P0 := Sylow.smul_eq_iff_mem_normalizer.2 x.2
  have htmem := Subgroup.mem_normalizer_iff.1 x.2
  have hkey : ∀ R R' : Sylow 7 G, R ≠ P0 → R' ≠ P0 → t • R = R → t • R' = R' → R' = R := by
    intro R R' hR hR' htR htR'
    obtain ⟨g, hg, rfl⟩ := hT R R' hR hR'
    have hc : t * g * t⁻¹ ∈ (P0 : Subgroup G) := (htmem g).1 hg
    have hh : g⁻¹ * (t * g * t⁻¹) ∈ (P0 : Subgroup G) := mul_mem (inv_mem hg) hc
    have hRt : t⁻¹ • R = R := by rw [inv_smul_eq_iff]; exact htR.symm
    have hh2 : (g⁻¹ * (t * g * t⁻¹)) • R = R := by
      rw [mul_smul, mul_smul, mul_smul, hRt, htR', inv_smul_smul]
    have hh3 := hA _ hh R hR hh2
    by_cases hg1 : g = 1
    · rw [hg1, one_smul]
    · exfalso
      have hcomm : t * g = g * t := by
        have : t * g * t⁻¹ = g := by
          have := hh3; rwa [inv_mul_eq_one, eq_comm] at this
        calc t * g = t * g * t⁻¹ * t := by group
          _ = g * t := by rw [this]
      have hz : Subgroup.zpowers g = P0 := hpr _ P0 ((Subgroup.zpowers_le).2 hg) (by simpa [Subgroup.zpowers_eq_bot] using hg1)
      have hall : ∀ k ∈ (P0 : Subgroup G), t * k = k * t := by
        intro k hk
        rw [← hz] at hk
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact ((Commute.zpow_right (show Commute t g from hcomm) j)).eq
      have : φ t = 1 := by
        refine Equiv.ext (fun y => ?_)
        show t • y = y
        by_cases hy : y = P0
        · rw [hy]; exact htP
        · obtain ⟨k, hk, rfl⟩ := hT R y hR hy
          rw [← mul_smul, hall k hk, mul_smul, htR]
      have := hinj (this.trans (map_one φ).symm)
      rw [this, orderOf_one] at ht
      omega
  have hσ : orderOf (φ t) = 2 := (orderOf_injective φ hinj t).trans ht
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := φ t) (by rw [hσ]; norm_num)
  have hsum : (φ t).cycleType.sum = 2*(n+1) := by
    rw [hn, hσ]; simp [Multiset.sum_replicate]; ring
  have hF := Equiv.Perm.card_fixedPoints (φ t)
  have hcX : Fintype.card (Sylow 7 G) = 8 := by rw [← Nat.card_eq_fintype_card]; exact hX
  rw [hcX, hsum] at hF
  have hfixeq : Fintype.card (Function.fixedPoints (φ t)) = (Finset.univ.filter fun y : Sylow 7 G => t • y = y).card := by
    rw [← Fintype.card_subtype]; rfl
  have hFge : 1 ≤ (Finset.univ.filter fun y : Sylow 7 G => t • y = y).card :=
    Finset.card_pos.2 ⟨P0, by simp [htP]⟩
  have hFle : (Finset.univ.filter fun y : Sylow 7 G => t • y = y).card ≤ 2 := by
    by_cases hq : ∃ Q : Sylow 7 G, Q ≠ P0 ∧ t • Q = Q
    · obtain ⟨Q, hQ, hQt⟩ := hq
      calc _ ≤ ({P0, Q} : Finset (Sylow 7 G)).card := by
            apply Finset.card_le_card
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            by_cases hyP : y = P0
            · simp [hyP]
            · simp [hkey Q y hQ hyP hQt hy]
        _ ≤ 2 := Finset.card_le_two
    · have : (Finset.univ.filter fun y : Sylow 7 G => t • y = y) ⊆ {P0} := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        by_contra hne
        exact hq ⟨y, by simpa using hne, hy⟩
      exact (Finset.card_le_card this).trans (by simp)
  have hs := hsign t
  rw [Equiv.Perm.sign_of_cycleType, hn, hσ, Multiset.sum_replicate, Multiset.card_replicate] at hs
  have hn2 : n = 2 := by omega
  subst hn2
  norm_num at hs

end Problem89
