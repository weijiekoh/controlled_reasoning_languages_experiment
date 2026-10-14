import Mathlib

/--
Let $G$ be a group of order $3825$. Prove that if $H$ is a normal subgroup of order $17$ in $G$,
then $H \leq Z(G)$.
-/
theorem le_center_of_card_eq_17_of_card_eq_3825 {G : Type} [Group G] (h : Nat.card G = 3825)
    (H : Subgroup G) [H.Normal] (hH : Nat.card H = 17) : H ≤ Subgroup.center G := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hHfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  have hGfin : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  letI := Fintype.ofFinite H
  letI := Fintype.ofFinite G
  have hcard : 17 ∣ Fintype.card H := by rw [← Nat.card_eq_fintype_card, hH]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 17 hcard
  have htop : Subgroup.zpowers x = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hx, hH]
  have hgen : ∀ y : H, ∃ m : ℤ, x ^ m = y := by
    intro y
    have hy : y ∈ Subgroup.zpowers x := by rw [htop]; trivial
    exact Subgroup.mem_zpowers_iff.mp hy
  let cj : G → MulAut H := fun g =>
    { toFun := fun y => ⟨g * y * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ y.2 g⟩
      invFun := fun y => ⟨g⁻¹ * y * g⁻¹⁻¹,Subgroup.Normal.conj_mem inferInstance _ y.2 g⁻¹⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let F : G →* MulAut H :=
    { toFun := cj
      map_one' := MulEquiv.ext fun y => Subtype.ext (by simp [cj])
      map_mul' := fun a b => MulEquiv.ext fun y => Subtype.ext (by simp [cj, mul_assoc]) }
  have key : ∀ σ : MulAut H, σ ^ 16 = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hgen (σ x)
    have hpow : ∀ k : ℕ, (σ ^ k) x = x ^ (m ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_zpow, ← hm, ← zpow_mul, pow_succ]
        congr 1
        ring
    have h2 : x ^ (m ^ 16) = x ^ (1 : ℤ) := by
      by_cases h17 : ((17 : ℕ) : ℤ) ∣ m
      · exfalso
        have h1 : x ^ m = 1 := by
          rw [← orderOf_dvd_iff_zpow_eq_one, hx]
          exact_mod_cast h17
        have h3 : σ x = 1 := by rw [← hm, h1]
        have h4 : x = 1 := by
          apply σ.injective
          rw [h3, map_one]
        have := hx
        rw [h4, orderOf_one] at this
        norm_num at this
      · rw [zpow_eq_zpow_iff_modEq, hx]
        have hm0 : (m : ZMod 17) ≠ 0 := by
          intro hc
          exact h17 (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd m 17).mp hc)
        have hp := ZMod.pow_card_sub_one_eq_one hm0
        norm_num at hp
        have h5 : ((m ^ 16 : ℤ) : ZMod 17) = ((1 : ℤ) : ZMod 17) := by
          push_cast
          rw [hp]
        have h6 := (ZMod.intCast_eq_intCast_iff _ _ 17).mp h5
        exact_mod_cast h6
    have hfix : (σ ^ 16) x = x := by
      rw [hpow 16, h2, zpow_one]
    have hall : ∀ y : H, (σ ^ 16) y = y := by
      intro y
      obtain ⟨k, hk⟩ := hgen y
      rw [← hk, map_zpow, hfix]
    exact MulEquiv.ext fun y => by rw [MulAut.one_apply]; exact hall y
  have hF : ∀ g : G, F g = 1 := by
    intro g
    have h1 : F g ^ 16 = 1 := key _
    have h2 : F g ^ 3825 = 1 := by
      rw [← map_pow]
      have : g ^ 3825 = 1 := by
        rw [← h, Nat.card_eq_fintype_card]
        exact pow_card_eq_one
      rw [this, map_one]
    have h3 : F g ^ Nat.gcd 3825 16 = 1 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
    norm_num at h3
    exact h3
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hz' : (F g) ⟨z, hz⟩ = ⟨z, hz⟩ := by rw [hF g]; rfl
  have h4 : g * z * g⁻¹ = z := congrArg Subtype.val hz'
  exact (mul_inv_eq_iff_eq_mul).mp h4
