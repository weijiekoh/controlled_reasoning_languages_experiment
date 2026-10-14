import Mathlib

open Polynomial

theorem card_gal_map_eq_eq_factorial {n : Nat} (hn : n > 4) (f : ℚ[X]) (hf : f.degree = n)
    (hf' : Irreducible f) (h : f.Gal ≃* (Equiv.Perm <| Fin n))
    {a b : SplittingField f} (ha : f.aeval a = 0) (hb : f.aeval b = 0) (neq : a ≠ b) :
    Nat.card {h : f.Gal // h a = b} = Nat.factorial (n - 1) := by
  classical
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hf
    exact absurd hf (by simp)
  have : Fact (map (algebraMap ℚ (SplittingField f)) f).Splits := ⟨SplittingField.splits f⟩
  have : Fintype f.Gal := Fintype.ofEquiv _ h.toEquiv.symm
  let _ := Polynomial.Gal.galAction f (SplittingField f)
  have := Polynomial.Gal.galAction_isPretransitive f (SplittingField f) hf'
  have hX : Nat.card (f.rootSet (SplittingField f)) = n := by
    have h1 := card_rootSet_eq_natDegree hf'.separable (SplittingField.splits f)
    rw [natDegree_eq_of_degree_eq_some hf] at h1
    rw [Nat.card_eq_fintype_card]; exact h1
  set x : (f.rootSet (SplittingField f)) := ⟨a, (mem_rootSet_of_ne hf0).2 ha⟩ with hxdef
  set y : (f.rootSet (SplittingField f)) := ⟨b, (mem_rootSet_of_ne hf0).2 hb⟩ with hydef
  have hsm : ∀ g : f.Gal, ((g • x : f.rootSet (SplittingField f)) : SplittingField f) = (g : SplittingField f ≃ₐ[ℚ] SplittingField f) x := by
    intro g
    have : Normal ℚ (SplittingField f) := SplittingField.instNormal f
    have h2 : Gal.restrict f (SplittingField f) g = g := by
      apply AlgEquiv.ext
      intro z
      have hc := AlgEquiv.restrictNormal_commutes (g : SplittingField f ≃ₐ[ℚ] SplittingField f) (SplittingField f) z
      simp only [Algebra.algebraMap_self, RingHom.id_apply] at hc
      exact hc
    have h1 := Polynomial.Gal.restrict_smul (p := f) (E := SplittingField f) g x
    rw [h2] at h1
    exact h1
  have hiff : ∀ g : f.Gal, g • x = y ↔ g a = b := fun g => by
    constructor
    · intro hg
      rw [← hsm g, hg]
    · intro hg
      exact Subtype.ext ((hsm g).trans hg)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq f.Gal x y
  have horb : MulAction.orbit f.Gal x = Set.univ := MulAction.orbit_eq_univ f.Gal x
  have hcard_orb : Nat.card (MulAction.orbit f.Gal x) = n := by
    rw [Nat.card_congr (Equiv.setCongr horb), Nat.card_congr (Equiv.Set.univ _), hX]
  have hcard_G : Nat.card f.Gal = n.factorial := by
    rw [Nat.card_congr h.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group f.Gal x
  simp only [← Nat.card_eq_fintype_card] at key
  rw [hcard_orb, hcard_G] at key
  have hstab : Nat.card (MulAction.stabilizer f.Gal x) = (n - 1).factorial := by
    have hn0 : n ≠ 0 := by omega
    have := Nat.mul_factorial_pred hn0
    rw [← this] at key
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) key
  rw [← hstab]
  refine Nat.card_congr
    { toFun := fun g => ⟨σ⁻¹ * g.1, ?_⟩
      invFun := fun t => ⟨σ * t.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [MulAction.mem_stabilizer_iff, mul_smul, (hiff g.1).2 g.2, ← hσ, inv_smul_smul]
  · exact (hiff _).1 (by rw [mul_smul, (MulAction.mem_stabilizer_iff.1 t.2), hσ])
  · intro g
    exact Subtype.ext (by simp)
  · intro t
    exact Subtype.ext (by simp)
