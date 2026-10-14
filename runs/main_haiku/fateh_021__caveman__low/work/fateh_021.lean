import Mathlib

/--
Prove that the order of Aut(Z_3 × Z_9) is 108.
-/
theorem card_addAut_eq_108 : Nat.card (AddAut <| ZMod 3 × ZMod 9) = 108 := by
  have hlift : ∀ (n : ℕ) [NeZero n] (z : ZMod 3 × ZMod 9) (hz : n • z = 0) (a : ZMod n),
      (ZMod.lift n ⟨zmultiplesHom (ZMod 3 × ZMod 9) z, by simpa using hz⟩ :
        ZMod n →+ (ZMod 3 × ZMod 9)) a = a.val • z := by
    intro n _ z hz a
    conv_lhs => rw [show a = ((a.val : ℤ) : ZMod n) by simp]
    rw [ZMod.lift_coe]
    simp [zmultiplesHom_apply]
  have key : ∀ (x y : ZMod 3 × ZMod 9), 3 • x = 0 → 9 • y = 0 →
      ∃ φ : (ZMod 3 × ZMod 9) →+ (ZMod 3 × ZMod 9),
        ∀ q : ZMod 3 × ZMod 9, φ q = q.1.val • x + q.2.val • y := by
    intro x y hx hy
    refine ⟨(ZMod.lift 3 ⟨zmultiplesHom _ x, by simpa using hx⟩).comp (AddMonoidHom.fst _ _)
      + (ZMod.lift 9 ⟨zmultiplesHom _ y, by simpa using hy⟩).comp (AddMonoidHom.snd _ _), ?_⟩
    intro q
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.coe_fst,
      AddMonoidHom.coe_snd]
    rw [hlift 3 x hx, hlift 9 y hy]
  have hq : ∀ (φ : AddAut (ZMod 3 × ZMod 9)) (q : ZMod 3 × ZMod 9),
      q.1.val • φ (1, 0) + q.2.val • φ (0, 1) = φ q := by
    intro φ q
    rw [← map_nsmul φ, ← map_nsmul φ, ← map_add]
    congr 1
    ext <;> simp
  have h3' : ∀ φ : AddAut (ZMod 3 × ZMod 9), 3 • φ (1, 0) = 0 := fun φ => by
    rw [← map_nsmul φ, (by decide : (3:ℕ) • ((1 : ZMod 3), (0 : ZMod 9)) = 0), map_zero]
  have h9' : ∀ φ : AddAut (ZMod 3 × ZMod 9), 9 • φ (0, 1) = 0 := fun φ => by
    rw [← map_nsmul φ, (by decide : (9:ℕ) • ((0 : ZMod 3), (1 : ZMod 9)) = 0), map_zero]
  have hinj' : ∀ φ : AddAut (ZMod 3 × ZMod 9),
      Function.Injective (fun q : ZMod 3 × ZMod 9 => q.1.val • φ (1, 0) + q.2.val • φ (0, 1)) := by
    intro φ a b hab
    apply φ.injective
    rw [← hq φ a, ← hq φ b]
    exact hab
  have hcard : Nat.card (AddAut (ZMod 3 × ZMod 9)) = Nat.card
      {xy : (ZMod 3 × ZMod 9) × (ZMod 3 × ZMod 9) //
        (3 • xy.1 = 0 ∧ 9 • xy.2 = 0) ∧
          Function.Injective (fun q : ZMod 3 × ZMod 9 => q.1.val • xy.1 + q.2.val • xy.2)} := by
    refine Nat.card_eq_of_bijective
      (fun φ => ⟨(φ (1, 0), φ (0, 1)), ⟨⟨h3' φ, h9' φ⟩, hinj' φ⟩⟩) ⟨?_, ?_⟩
    · intro φ ψ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply AddEquiv.ext
      intro q
      rw [← hq φ q, ← hq ψ q, h1, h2]
    · rintro ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hinj⟩⟩
      obtain ⟨φ, hφ⟩ := key x y hx hy
      have hinjφ : Function.Injective φ := by
        intro a b hab
        apply hinj
        show a.1.val • x + a.2.val • y = b.1.val • x + b.2.val • y
        rw [← hφ a, ← hφ b]
        exact hab
      have hb : Function.Bijective φ := Finite.injective_iff_bijective.mp hinjφ
      refine ⟨AddEquiv.ofBijective φ hb, Subtype.ext (Prod.ext ?_ ?_)⟩
      · show φ (1, 0) = x
        rw [hφ, show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 9).val = 0 from rfl]; simp
      · show φ (0, 1) = y
        rw [hφ, show (1 : ZMod 9).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl]; simp
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel
