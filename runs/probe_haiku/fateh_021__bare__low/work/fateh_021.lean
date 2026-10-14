import Mathlib

/--
Prove that the order of Aut(Z_3 × Z_9) is 108.
-/
theorem card_addAut_eq_108 : Nat.card (AddAut <| ZMod 3 × ZMod 9) = 108 := by
  set S : Finset ((ZMod 3 × ZMod 9) × (ZMod 3 × ZMod 9)) :=
    (Finset.univ).filter (fun p => (3:ℕ) • p.1 = 0 ∧
      ∀ q : ZMod 3 × ZMod 9, q.1.val • p.1 + q.2.val • p.2 = 0 → q = 0) with hS
  have hcard : S.card = 108 := by
    rw [hS]
    set_option maxRecDepth 100000 in
    set_option maxHeartbeats 4000000 in
    decide
  have hdecomp : ∀ q : ZMod 3 × ZMod 9,
      q = q.1.val • ((1:ZMod 3), (0:ZMod 9)) + q.2.val • ((0:ZMod 3), (1:ZMod 9)) := by
    intro q
    ext <;> simp
  have hform : ∀ f : AddAut (ZMod 3 × ZMod 9), ∀ q : ZMod 3 × ZMod 9,
      f q = q.1.val • f (1,0) + q.2.val • f (0,1) := by
    intro f q
    conv_lhs => rw [hdecomp q]
    rw [map_add, map_nsmul, map_nsmul]
  have h9 : ∀ z : ZMod 3 × ZMod 9, ((9:ℕ):ℤ) • z = 0 := by decide
  have hequiv : AddAut (ZMod 3 × ZMod 9) ≃ {p // p ∈ S} := by
    refine Equiv.ofBijective (fun f => ⟨(f (1,0), f (0,1)), ?_⟩) ⟨?_, ?_⟩
    · rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · dsimp only
        have e : (3:ℕ) • ((1:ZMod 3), (0:ZMod 9)) = 0 := by decide
        rw [← map_nsmul, e, map_zero]
      · dsimp only
        intro q hq
        have : f q = 0 := by rw [hform f q]; exact hq
        exact (map_eq_zero_iff f f.injective).1 this
    · intro f g hfg
      have h1 := congrArg (fun p => p.1.1) hfg
      have h2 := congrArg (fun p => p.1.2) hfg
      dsimp only at h1 h2
      apply AddEquiv.ext; intro q
      rw [hform f q, hform g q, h1, h2]
    · rintro ⟨⟨x, y⟩, hxy⟩
      rw [hS, Finset.mem_filter] at hxy
      obtain ⟨-, h3, hker⟩ := hxy
      have h3' : ((3:ℕ):ℤ) • x = 0 := by rw [natCast_zsmul]; exact h3
      obtain ⟨L3, hL3⟩ : ∃ L : ZMod 3 →+ (ZMod 3 × ZMod 9), ∀ z : ℤ, L (z : ZMod 3) = z • x :=
        ⟨ZMod.lift 3 ⟨zmultiplesHom _ x, by rw [zmultiplesHom_apply]; exact h3'⟩,
         fun z => by rw [ZMod.lift_coe]; simp⟩
      obtain ⟨L9, hL9⟩ : ∃ L : ZMod 9 →+ (ZMod 3 × ZMod 9), ∀ z : ℤ, L (z : ZMod 9) = z • y :=
        ⟨ZMod.lift 9 ⟨zmultiplesHom _ y, by rw [zmultiplesHom_apply]; exact h9 y⟩,
         fun z => by rw [ZMod.lift_coe]; simp⟩
      obtain ⟨hm, hm1, hm2⟩ : ∃ hm : (ZMod 3 × ZMod 9) →+ (ZMod 3 × ZMod 9),
          hm (1,0) = x ∧ hm (0,1) = y := by
        refine ⟨AddMonoidHom.coprod L3 L9, ?_, ?_⟩
        · rw [AddMonoidHom.coprod_apply]
          have a := hL3 1
          have b := hL9 0
          simp only [Int.cast_one, one_smul] at a
          simp only [Int.cast_zero, zero_smul] at b
          simp [a, b]
        · rw [AddMonoidHom.coprod_apply]
          have a := hL3 0
          have b := hL9 1
          simp only [Int.cast_one, one_smul, Int.cast_zero, zero_smul] at a b
          simp [a, b]
      have hmform : ∀ q : ZMod 3 × ZMod 9, hm q = q.1.val • x + q.2.val • y := by
        intro q
        conv_lhs => rw [hdecomp q]
        rw [map_add, map_nsmul, map_nsmul, hm1, hm2]
      have hinj : Function.Injective hm := by
        rw [injective_iff_map_eq_zero]
        intro a ha
        rw [hmform] at ha
        exact hker a ha
      have hbij : Function.Bijective hm := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
      exact ⟨AddEquiv.ofBijective hm hbij, Subtype.ext (Prod.ext hm1 hm2)⟩
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
