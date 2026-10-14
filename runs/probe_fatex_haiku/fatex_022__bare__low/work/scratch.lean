import Mathlib
open Polynomial in
example (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] [IsGalois ℚ F] (x : F) (α : ℂ)
    (hα : aeval α (minpoly ℚ x) = 0) : α ∈ F := by
  have hs := Normal.splits (inferInstance : Normal ℚ F) x
  rw [Polynomial.splits_iff_exists_multiset] at hs
  obtain ⟨s, hs⟩ := hs
  have h2 := congrArg (Polynomial.map (algebraMap F ℂ)) hs
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h2
  have h3 := congrArg (Polynomial.eval α) h2
  rw [Polynomial.eval_map, ← Polynomial.aeval_def, hα] at h3
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.map_sub, Polynomial.map_X, Function.comp_def, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_sub, Polynomial.eval_X] at h3
  have hmon : (map (algebraMap ℚ F) (minpoly ℚ x)).Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _
  have hlc : (algebraMap F ℂ) (map (algebraMap ℚ F) (minpoly ℚ x)).leadingCoeff ≠ 0 := by
    rw [hmon.leadingCoeff, map_one]; exact one_ne_zero
  have h4 := h3.symm
  rw [mul_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact absurd h4 hlc
  · rw [Multiset.prod_eq_zero_iff] at h4
    obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h4
    have : α = algebraMap F ℂ a := by rw [sub_eq_zero] at ha; exact ha
    rw [this]; exact a.2

open Polynomial in
example (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] [IsGalois ℚ F] (x : F)
    (hmem : ∀ (x : F) (α : ℂ), aeval α (minpoly ℚ x) = 0 → α ∈ F) : True := by
  have hconj : ∀ x : F, starRingEnd ℂ (x : ℂ) ∈ F := by
    intro x
    apply hmem x
    have hx : aeval (x : ℂ) (minpoly ℚ x) = 0 := by
      have := minpoly.aeval ℚ x
      have h := congrArg F.val this
      rw [← Polynomial.aeval_algHom_apply] at h
      simpa using h
    have key : starRingEnd ℂ (aeval (x : ℂ) (minpoly ℚ x)) = aeval (starRingEnd ℂ (x : ℂ)) (minpoly ℚ x) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext (fun q => by simp)
    rw [← key, hx, map_zero]
  trivial
