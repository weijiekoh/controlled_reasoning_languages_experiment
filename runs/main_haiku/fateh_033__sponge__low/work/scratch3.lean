import Mathlib

open Polynomial

theorem card_gal_map_eq_eq_factorial {n : Nat} (hn : n > 4) (f : ℚ[X]) (hf : f.degree = n)
    (hf' : Irreducible f) (h : f.Gal ≃* (Equiv.Perm <| Fin n))
    {a b : SplittingField f} (ha : f.aeval a = 0) (hb : f.aeval b = 0) (neq : a ≠ b) :
    Nat.card {h : f.Gal // h a = b} = Nat.factorial (n - 1) := by
  have hf0 : f ≠ 0 := by
    intro h0
    simp [h0] at hf
  have hsplit : Fact ((map (algebraMap ℚ f.SplittingField) f).Splits) :=
    ⟨by exact SplittingField.splits f⟩
  letI act : MulAction f.Gal (f.rootSet f.SplittingField) :=
    Polynomial.Gal.galAction f f.SplittingField
  have : MulAction.IsPretransitive f.Gal (f.rootSet f.SplittingField) :=
    Polynomial.Gal.galAction_isPretransitive f _ hf'
  have hcardR : Nat.card (f.rootSet f.SplittingField) = n := by
    have := card_rootSet_eq_natDegree hf'.separable (SplittingField.splits f)
    rw [natDegree_eq_of_degree_eq_some hf] at this
    rw [Nat.card_eq_fintype_card]
    exact this
  have hG : Nat.card f.Gal = n.factorial := by
    rw [Nat.card_congr h.toEquiv, Nat.card_perm, Nat.card_fin]
  have ha' : a ∈ f.rootSet f.SplittingField := mem_rootSet.2 ⟨hf0, ha⟩
  have hb' : b ∈ f.rootSet f.SplittingField := mem_rootSet.2 ⟨hf0, hb⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq f.Gal
    (⟨a, ha'⟩ : f.rootSet f.SplittingField) ⟨b, hb'⟩
  have key : ∀ g : f.Gal, g a = b ↔
      g • (⟨a, ha'⟩ : f.rootSet f.SplittingField) = ⟨b, hb'⟩ := by
    intro g
    rw [Subtype.ext_iff]
    have e : Subtype.val (g • (⟨a, ha'⟩ : f.rootSet f.SplittingField)) = g a := by
      exact @Gal.restrict_smul ℚ _ f f.SplittingField _ _ hsplit g (⟨a, ha'⟩ : f.rootSet f.SplittingField)
    rw [e]
  have hfiber : Nat.card {g : f.Gal // g a = b} =
      Nat.card (MulAction.stabilizer f.Gal (⟨a, ha'⟩ : f.rootSet f.SplittingField)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft c⁻¹) ?_)
    intro g
    rw [key, MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      show (c⁻¹ * g) • (⟨a, ha'⟩ : f.rootSet f.SplittingField) = ⟨a, ha'⟩
      rw [mul_smul, hg, ← hc, inv_smul_smul]
    · intro hs
      have hs' : (c⁻¹ * g) • (⟨a, ha'⟩ : f.rootSet f.SplittingField) = ⟨a, ha'⟩ := hs
      have e : g • (⟨a, ha'⟩ : f.rootSet f.SplittingField)
          = c • ((c⁻¹ * g) • (⟨a, ha'⟩ : f.rootSet f.SplittingField)) := by
        rw [mul_smul, smul_inv_smul]
      rw [e, hs']
      exact hc
  have hidx : (MulAction.stabilizer f.Gal (⟨a, ha'⟩ : f.rootSet f.SplittingField)).index = n := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, hcardR]
  have hmul := (MulAction.stabilizer f.Gal (⟨a, ha'⟩ : f.rootSet f.SplittingField)).card_mul_index
  rw [hidx, hG] at hmul
  rw [hfiber]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ] at hmul
  simp only [Nat.add_sub_cancel]
  have hpos : (m + 1) > 0 := by omega
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [mul_comm]
  exact hmul
