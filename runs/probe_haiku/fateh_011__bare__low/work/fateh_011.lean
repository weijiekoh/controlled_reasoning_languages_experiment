import Mathlib

/--
Let $G$ be a group of order $3825$. Prove that if $H$ is a normal subgroup of order $17$ in $G$,
then $H \leq Z(G)$.
-/
theorem le_center_of_card_eq_17_of_card_eq_3825 {G : Type} [Group G] (h : Nat.card G = 3825)
    (H : Subgroup G) [H.Normal] (hH : Nat.card H = 17) : H ≤ Subgroup.center G := by
  classical
  have hG : ∀ g : G, g ^ 3825 = 1 := fun g => by
    rw [← h]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard g)
  have : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hHgt : 1 < Nat.card H := by rw [hH]; norm_num
  have hnt : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp hHgt
  obtain ⟨y, hy⟩ := exists_ne (1 : H)
  have hord : orderOf y = 17 := by
    have h1 : orderOf y ∣ 17 := hH ▸ orderOf_dvd_natCard y
    rcases (Nat.dvd_prime (by norm_num)).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hy
    · exact h2
  have hxH : (y : G) ∈ H := y.2
  have hx17 : orderOf (y : G) = 17 := by
    rw [Subgroup.orderOf_coe, hord]
  have hHx : Subgroup.zpowers (y : G) = H :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxH)
      (le_of_eq (by rw [Nat.card_zpowers, hx17, hH]))
  have hkey : ∀ g : G, g * (y : G) * g⁻¹ = (y : G) := by
    intro g
    have hmem : g * (y : G) * g⁻¹ ∈ Subgroup.zpowers (y : G) := by
      rw [hHx]; exact Subgroup.Normal.conj_mem ‹H.Normal› _ hxH g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hpow : ∀ n : ℕ, (g ^ n) * (y : G) * (g ^ n)⁻¹ = (y : G) ^ (m ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : g ^ (n+1) * (y : G) * (g ^ (n+1))⁻¹ = g ^ n * (g * (y : G) * g⁻¹) * (g ^ n)⁻¹ := by
          group
        rw [e, ← hm, ← conj_zpow, ih, ← zpow_mul, pow_succ]
    have h3 := hpow 3825
    rw [hG g] at h3
    simp at h3
    have hunit : (y : G) ^ (m ^ 3825 - 1) = 1 := by
      rw [zpow_sub_one, ← h3, mul_inv_cancel]
    have hdiv : (orderOf (y : G) : ℤ) ∣ m ^ 3825 - 1 :=
      orderOf_dvd_iff_zpow_eq_one.mpr hunit
    rw [hx17] at hdiv
    push_cast at hdiv
    have key : ∀ a : ZMod 17, a ^ 3825 = a := by
      set_option maxRecDepth 100000 in decide
    have hz : ((m ^ 3825 - 1 : ℤ) : ZMod 17) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mpr (by exact_mod_cast hdiv)
    push_cast at hz
    have hm1 : ((m : ℤ) : ZMod 17) = 1 := by
      have := key (m : ZMod 17)
      rw [sub_eq_zero] at hz
      rw [hz] at this
      exact this.symm
    have hdvd : (17 : ℤ) ∣ m - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp
      push_cast
      rw [hm1, sub_self]
    have hm0 : (y : G) ^ (m - 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx17]; exact_mod_cast hdvd)
    have hxm : (y : G) ^ m = (y : G) := by
      rw [show m = m - 1 + 1 by ring, zpow_add, hm0, one_mul, zpow_one]
    rw [← hm, hxm]
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  rw [← hHx] at hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hgx : g * (y : G) * g⁻¹ = (y : G) := hkey g
  have hcomm : Commute g (y : G) := by
    unfold Commute SemiconjBy
    rw [mul_inv_eq_iff_eq_mul] at hgx
    exact hgx
  exact (hcomm.zpow_right k).eq
