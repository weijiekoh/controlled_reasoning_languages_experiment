import Mathlib

/--
Let $G$ be a group of order $3825$. Prove that if $H$ is a normal subgroup of order $17$ in $G$,
then $H \leq Z(G)$.
-/
theorem le_center_of_card_eq_17_of_card_eq_3825 {G : Type} [Group G] (h : Nat.card G = 3825)
    (H : Subgroup G) [H.Normal] (hH : Nat.card H = 17) : H ≤ Subgroup.center G := by
  classical
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  obtain ⟨h0, hh0⟩ := exists_prime_orderOf_dvd_card' 17 (by rw [hH])
  have hz : Subgroup.zpowers h0 = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hh0, hH])
  have hgen : ∀ x : H, ∃ k : ℤ, h0 ^ k = x := fun x => by
    have : x ∈ Subgroup.zpowers h0 := by rw [hz]; trivial
    exact Subgroup.mem_zpowers_iff.mp this
  have hG17 : orderOf (h0 : G) = 17 := by rw [Subgroup.orderOf_coe, hh0]
  have hmem : ∀ g : G, g * (h0 : G) * g⁻¹ ∈ H :=
    fun g => Subgroup.Normal.conj_mem inferInstance _ h0.2 g
  have hcz : ∀ (g : G) (m : ℤ), g * (h0 : G) ^ m * g⁻¹ = (g * (h0 : G) * g⁻¹) ^ m := by
    intro g m
    have := map_zpow (MulAut.conj g) (h0 : G) m
    simpa [MulAut.conj_apply] using this.symm
  have hirr : Irreducible (17 : ℤ) :=
    (Int.prime_iff_natAbs_prime.mpr (by norm_num)).irreducible
  have hcomm : ∀ g : G, g * (h0 : G) = (h0 : G) * g := by
    intro g
    obtain ⟨a, ha⟩ := hgen ⟨g * (h0 : G) * g⁻¹, hmem g⟩
    have hA : g * (h0 : G) * g⁻¹ = (h0 : G) ^ a := by
      have := congrArg Subtype.val ha
      simpa using this.symm
    have hgn : g ^ 3825 = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [← h]
      exact orderOf_dvd_natCard g
    have key : ∀ n : ℕ, g ^ n * (h0 : G) * (g ^ n)⁻¹ = (h0 : G) ^ (a ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : g ^ (n + 1) * (h0 : G) * (g ^ (n + 1))⁻¹
            = g * (g ^ n * (h0 : G) * (g ^ n)⁻¹) * g⁻¹ := by group
        rw [e, ih, hcz, hA, ← zpow_mul]
        congr 1
        ring
    have k3 : (h0 : G) = (h0 : G) ^ (a ^ 3825) := by
      have := key 3825
      rw [hgn, one_mul, inv_one, mul_one] at this
      exact this
    have hpow : (h0 : G) ^ (a ^ 3825 - 1) = 1 := by
      rw [zpow_sub_one, ← k3, mul_inv_cancel]
    have d1 : (17 : ℤ) ∣ a ^ 3825 - 1 := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hpow
      rw [hG17] at this
      exact_mod_cast this
    have hnd : ¬ (17 : ℤ) ∣ a := by
      intro hd
      have hpa : (h0 : G) ^ a = 1 := by
        apply orderOf_dvd_iff_zpow_eq_one.mp
        rw [hG17]
        exact_mod_cast hd
      rw [hpa] at hA
      have h1 : (h0 : G) = 1 := by
        calc (h0 : G) = g⁻¹ * (g * (h0 : G) * g⁻¹) * g := by group
          _ = 1 := by rw [hA]; group
      have := hG17
      rw [h1, orderOf_one] at this
      norm_num at this
    have hcop : IsCoprime a 17 := ((Irreducible.coprime_iff_not_dvd hirr).mpr hnd).symm
    have h16 : a ^ (17 - 1) ≡ 1 [ZMOD 17] :=
      Int.ModEq.pow_card_sub_one_eq_one (by norm_num) hcop
    have h16' : a ^ 16 ≡ 1 [ZMOD 17] := by simpa using h16
    have h3 : a ^ 3825 ≡ 1 [ZMOD 17] := by
      exact Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp d1)
    have e : a ^ 3825 = a * (a ^ 16) ^ 239 := by ring
    have h1 : a ≡ 1 [ZMOD 17] := by
      have h2 : a * (a ^ 16) ^ 239 ≡ a * 1 ^ 239 [ZMOD 17] :=
        (h16'.pow 239).mul_left a
      rw [one_pow, mul_one] at h2
      rw [e] at h3
      exact h2.symm.trans h3
    have hd1 : (17 : ℤ) ∣ 1 - a := Int.ModEq.dvd h1
    have hpa : (h0 : G) ^ (1 - a) = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.mp
      rw [hG17]
      exact_mod_cast hd1
    rw [zpow_sub, zpow_one] at hpa
    have hfix : (h0 : G) ^ a = (h0 : G) := (mul_inv_eq_one.mp hpa).symm
    have hA' : g * (h0 : G) * g⁻¹ = (h0 : G) := hA.trans hfix
    exact mul_inv_eq_iff_eq_mul.mp hA'
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k, hk⟩ := hgen ⟨x, hx⟩
  have hxk : x = (h0 : G) ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  rw [hxk]
  have hc : Commute g (h0 : G) := hcomm g
  exact (hc.zpow_right k).eq
