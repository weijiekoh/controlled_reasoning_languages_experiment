import Mathlib

/--
Prove that the order of Aut(Z_3 × Z_9) is 108.
-/
theorem card_addAut_eq_108 : Nat.card (AddAut <| ZMod 3 × ZMod 9) = 108 := by
  classical
  have formula : ∀ g : ZMod 3 × ZMod 9 →+ ZMod 3 × ZMod 9, ∀ x : ZMod 3 × ZMod 9,
      g x = x.1.val • g (1,0) + x.2.val • g (0,1) := by
    intro g x
    have hx : x = x.1.val • ((1:ZMod 3),(0:ZMod 9)) + x.2.val • ((0:ZMod 3),(1:ZMod 9)) := by
      ext <;> simp [nsmul_eq_mul]
    conv_lhs => rw [hx]
    rw [map_add, map_nsmul, map_nsmul]
  have hc : Nat.card {p : (ZMod 3 × ZMod 9) × (ZMod 3 × ZMod 9) // 3 • p.1 = 0 ∧ 9 • p.2 = 0 ∧
      ∀ x : ZMod 3 × ZMod 9, x.1.val • p.1 + x.2.val • p.2 = 0 → x = 0} = 108 := by
    rw [Nat.card_eq_fintype_card]; set_option maxRecDepth 100000 in decide +kernel
  rw [← hc]
  have mkhom : ∀ p : (ZMod 3 × ZMod 9) × (ZMod 3 × ZMod 9), 3 • p.1 = 0 → 9 • p.2 = 0 →
      ∃ h : ZMod 3 × ZMod 9 →+ ZMod 3 × ZMod 9, h (1,0) = p.1 ∧ h (0,1) = p.2 := by
    intro p h3 h9
    let ψ1 : ZMod 3 →+ ZMod 3 × ZMod 9 := ZMod.lift 3 ⟨zmultiplesHom _ p.1, by
      simpa [zmultiplesHom_apply] using h3⟩
    let ψ2 : ZMod 9 →+ ZMod 3 × ZMod 9 := ZMod.lift 9 ⟨zmultiplesHom _ p.2, by
      simpa [zmultiplesHom_apply] using h9⟩
    have e1 : ψ1 1 = p.1 := by
      have := ZMod.lift_coe 3 ⟨zmultiplesHom _ p.1, by simpa [zmultiplesHom_apply] using h3⟩ (1:ℤ)
      simpa [ψ1] using this
    have e2 : ψ2 1 = p.2 := by
      have := ZMod.lift_coe 9 ⟨zmultiplesHom _ p.2, by simpa [zmultiplesHom_apply] using h9⟩ (1:ℤ)
      simpa [ψ2] using this
    refine ⟨AddMonoidHom.coprod ψ1 ψ2, ?_, ?_⟩
    · simp [AddMonoidHom.coprod_apply, e1]
    · simp [AddMonoidHom.coprod_apply, e2]
  have hbij : ∀ (h : ZMod 3 × ZMod 9 →+ ZMod 3 × ZMod 9) (u v : ZMod 3 × ZMod 9),
      h (1,0) = u → h (0,1) = v → (∀ x : ZMod 3 × ZMod 9, x.1.val • u + x.2.val • v = 0 → x = 0) →
      Function.Bijective h := by
    intro h u v hu hv hx
    apply Finite.injective_iff_bijective.mp
    rw [injective_iff_map_eq_zero]
    intro x hx0
    apply hx x
    rw [← hu, ← hv, ← formula h x]
    exact hx0
  have hfz : ∀ f : AddAut (ZMod 3 × ZMod 9), 3 • f (1,0) = 0 ∧ 9 • f (0,1) = 0 := by
    intro f
    constructor
    · rw [← map_nsmul]
      convert map_zero f
      decide
    · rw [← map_nsmul]
      convert map_zero f
      decide
  apply Nat.card_congr
  refine ⟨fun f => ⟨(f (1,0), f (0,1)), (hfz f).1, (hfz f).2, ?_⟩,
    fun p => AddEquiv.ofBijective
      (Classical.choose (mkhom p.1 p.2.1 p.2.2.1)) (by
        obtain ⟨hu, hv⟩ := Classical.choose_spec (mkhom p.1 p.2.1 p.2.2.1)
        exact hbij _ p.1.1 p.1.2 hu hv p.2.2.2), ?_, ?_⟩
  · intro x hx
    dsimp only at hx
    have h2 : (f : ZMod 3 × ZMod 9 →+ ZMod 3 × ZMod 9) x = 0 := by
      rw [formula (f : ZMod 3 × ZMod 9 →+ ZMod 3 × ZMod 9) x]; exact hx
    exact (injective_iff_map_eq_zero (f : ZMod 3 × ZMod 9 →+ ZMod 3 × ZMod 9)).1 f.injective x h2
  · intro f
    apply AddEquiv.ext
    intro x
    obtain ⟨hu, hv⟩ := Classical.choose_spec (mkhom (f (1,0), f (0,1)) (hfz f).1 (hfz f).2)
    dsimp only at hu hv
    simp only [AddEquiv.ofBijective_apply]
    rw [formula (Classical.choose (mkhom (f (1,0), f (0,1)) (hfz f).1 (hfz f).2)) x, hu, hv]
    exact (formula (f : ZMod 3 × ZMod 9 →+ ZMod 3 × ZMod 9) x).symm
  · intro p
    apply Subtype.ext
    obtain ⟨hu, hv⟩ := Classical.choose_spec (mkhom p.1 p.2.1 p.2.2.1)
    exact Prod.ext hu hv
