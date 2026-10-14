import Mathlib

/--
Let $G$ be a group of order $3825$. Prove that if $H$ is a normal subgroup of order $17$ in $G$,
then $H \leq Z(G)$.
-/
theorem le_center_of_card_eq_17_of_card_eq_3825 {G : Type} [Group G] (h : Nat.card G = 3825)
    (H : Subgroup G) [H.Normal] (hH : Nat.card H = 17) : H ≤ Subgroup.center G := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have : IsCyclic H := isCyclic_of_prime_card hH
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  have key : ∀ g : G, ∀ x : G, x ∈ H → g * x * g⁻¹ ∈ H :=
    fun g x hx => Subgroup.Normal.conj_mem ‹H.Normal› x hx g
  let φ : G →* MulAut H :=
    { toFun := fun g =>
        { toFun := fun x => ⟨g * x * g⁻¹, key g x.1 x.2⟩
          invFun := fun x => ⟨g⁻¹ * x * g⁻¹⁻¹, by
            have := key g⁻¹ x.1 x.2
            simpa using this⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc])
          map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
      map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun g g' => MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
  have hR1 : Nat.card φ.range ∣ 3825 := by
    rw [← h, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hR2 : Nat.card φ.range ∣ 16 := by
    have := Subgroup.card_subgroup_dvd_card φ.range
    rw [IsCyclic.card_mulAut H, hH] at this
    rw [Nat.totient_prime (by norm_num)] at this
    exact this
  have hR3 : Nat.card φ.range = 1 := by
    have hd : Nat.card φ.range ∣ Nat.gcd 3825 16 := Nat.dvd_gcd hR1 hR2
    rw [show Nat.gcd 3825 16 = 1 by norm_num] at hd
    exact Nat.dvd_one.mp hd
  have hsub : Subsingleton φ.range := Nat.card_eq_one_iff_unique.mp hR3 |>.1
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : φ g = 1 := by
    have : (⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : φ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have hx' : φ g ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [hg]; rfl
  have := congrArg Subtype.val hx'
  change g * x * g⁻¹ = x at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this
