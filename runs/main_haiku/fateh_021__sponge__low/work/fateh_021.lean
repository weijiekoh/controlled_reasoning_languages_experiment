import Mathlib

/--
Prove that the order of Aut(Z_3 × Z_9) is 108.
-/
theorem card_addAut_eq_108 : Nat.card (AddAut <| ZMod 3 × ZMod 9) = 108 := by
  have hmod : ∀ (M : Type) [AddCommGroup M] (p : M) (m n : ℕ), m • p = 0 → (n % m) • p = n • p := by
    intro M _ p m n h
    conv_rhs => rw [← Nat.mod_add_div n m]
    have hk : (m * (n / m)) • p = 0 := by
      rw [mul_comm, mul_nsmul', h, smul_zero]
    rw [add_nsmul, hk, add_zero]
  obtain ⟨Gh, hGh⟩ : ∃ Gh : ∀ p q : ZMod 3 × ZMod 9, 3 • p = 0 → 9 • q = 0 →
      (ZMod 3 × ZMod 9) →+ (ZMod 3 × ZMod 9),
      ∀ p q h3 h9 x, Gh p q h3 h9 x = x.1.val • p + x.2.val • q := by
    refine ⟨fun p q h3 h9 => AddMonoidHom.mk' (fun x => x.1.val • p + x.2.val • q) ?_,
      fun _ _ _ _ _ => rfl⟩
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [hmod _ p 3 _ h3, hmod _ q 9 _ h9, add_nsmul, add_nsmul]
    abel
  have hid : ∀ x : ZMod 3 × ZMod 9,
      x = x.1.val • ((1 : ZMod 3), (0 : ZMod 9)) + x.2.val • ((0 : ZMod 3), (1 : ZMod 9)) := by
    decide
  have hfw : ∀ φ : AddAut (ZMod 3 × ZMod 9),
      3 • φ ((1 : ZMod 3), (0 : ZMod 9)) = 0 ∧ 9 • φ ((0 : ZMod 3), (1 : ZMod 9)) = 0 ∧
      ∀ x : ZMod 3 × ZMod 9, x.1.val • φ ((1 : ZMod 3), (0 : ZMod 9))
        + x.2.val • φ ((0 : ZMod 3), (1 : ZMod 9)) = 0 → x = 0 := by
    intro φ
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_nsmul, show (3 : ℕ) • ((1 : ZMod 3), (0 : ZMod 9)) = 0 from by decide, map_zero]
    · rw [← map_nsmul, show (9 : ℕ) • ((0 : ZMod 3), (1 : ZMod 9)) = 0 from by decide, map_zero]
    · intro x hx
      have h1 : φ x = 0 := by
        conv_lhs => rw [hid x]
        rw [map_add, map_nsmul, map_nsmul]
        exact hx
      exact φ.injective (h1.trans (map_zero φ).symm)
  have hbij : ∀ (p q : ZMod 3 × ZMod 9) (h3 : 3 • p = 0) (h9 : 9 • q = 0),
      (∀ x : ZMod 3 × ZMod 9, x.1.val • p + x.2.val • q = 0 → x = 0) →
      Function.Bijective (Gh p q h3 h9) := by
    intro p q h3 h9 hk
    have inj : Function.Injective (Gh p q h3 h9) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply hk
      rw [← hGh p q h3 h9 x]
      exact hx
    exact ⟨inj, Finite.surjective_of_injective inj⟩
  have e1 : (ZMod.val (1 : ZMod 3)) = 1 := rfl
  have e2 : (ZMod.val (0 : ZMod 9)) = 0 := rfl
  have e3 : (ZMod.val (0 : ZMod 3)) = 0 := rfl
  have e4 : (ZMod.val (1 : ZMod 9)) = 1 := rfl
  have hcard : Nat.card (AddAut (ZMod 3 × ZMod 9)) = Nat.card
      {pq : (ZMod 3 × ZMod 9) × (ZMod 3 × ZMod 9) // 3 • pq.1 = 0 ∧ 9 • pq.2 = 0 ∧
        ∀ x : ZMod 3 × ZMod 9, x.1.val • pq.1 + x.2.val • pq.2 = 0 → x = 0} := by
    refine Nat.card_congr
      { toFun := fun φ => ⟨((φ ((1 : ZMod 3), (0 : ZMod 9))), φ ((0 : ZMod 3), (1 : ZMod 9))), hfw φ⟩
        invFun := fun s => AddEquiv.ofBijective (Gh s.1.1 s.1.2 s.2.1 s.2.2.1) (hbij _ _ _ _ s.2.2.2)
        left_inv := ?_
        right_inv := ?_ }
    · intro φ
      refine AddEquiv.ext (fun x => ?_)
      rw [AddEquiv.ofBijective_apply, hGh]
      conv_rhs => rw [hid x]
      rw [map_add, map_nsmul, map_nsmul]
    · rintro ⟨⟨p, q⟩, h⟩
      apply Subtype.ext
      simp only [AddEquiv.ofBijective_apply, hGh, e1, e2, e3, e4, one_smul, zero_smul,
        zero_add, add_zero]
  rw [hcard, Nat.card_eq_fintype_card]
  set_option maxRecDepth 100000 in decide
