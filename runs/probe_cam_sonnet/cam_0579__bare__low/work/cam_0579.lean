import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-579»

open scoped BigOperators
theorem convexOn_iff_convex_and_hessian_posSemidef
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (_hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x) :
    ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ z : Fin n → ℝ,
        0 ≤
          ∑ i : Fin n, z i *
            ∑ j : Fin n,
              z j *
                ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
                  (Pi.single i (1 : ℝ))) := by
  have hd : ∀ y ∈ C, DifferentiableAt ℝ (fderiv ℝ f) y := fun y hy =>
    ((_hC2 y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hS : ∀ y ∈ C, ∀ z : Fin n → ℝ,
      (∑ i : Fin n, z i * ∑ j : Fin n, z j *
        ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) y) (Pi.single i (1 : ℝ))))
      = fderiv ℝ (fderiv ℝ f) y z z := by
    intro y hy z
    have h1 : ∀ j : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j (1:ℝ))) y
        = (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1:ℝ))).comp (fderiv ℝ (fderiv ℝ f) y) :=
      fun j => by
        have hA := (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1:ℝ))).hasFDerivAt (x := fderiv ℝ f y)
        exact (hA.comp y (hd y hy).hasFDerivAt).fderiv
    have hz : z = ∑ i, z i • (Pi.single i (1:ℝ) : Fin n → ℝ) := by
      ext k; simp [Pi.single_apply]
    simp only [h1]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    conv_rhs => rw [hz]
    simp [map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have key : ∀ (a z : Fin n → ℝ) (t : ℝ), a + t • z ∈ C →
      HasDerivAt (fun s : ℝ => f (a + s • z)) (fderiv ℝ f (a + t • z) z) t ∧
      HasDerivAt (fun s : ℝ => fderiv ℝ f (a + s • z) z)
        (fderiv ℝ (fderiv ℝ f) (a + t • z) z z) t := by
    intro a z t ht
    have hl : HasDerivAt (fun s : ℝ => a + s • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add a
    have hfd : HasFDerivAt f (fderiv ℝ f (a + t • z)) (a + t • z) :=
      ((_hC2 _ ht).differentiableAt (by norm_num)).hasFDerivAt
    refine ⟨hfd.comp_hasDerivAt t hl, ?_⟩
    have := ((ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt.comp (a + t • z)
        (hd _ ht).hasFDerivAt).comp_hasDerivAt t hl
    exact this
  have hopen : ∀ (a z : Fin n → ℝ), IsOpen {s : ℝ | a + s • z ∈ C} := fun a z =>
    hCopen.preimage (by fun_prop)
  constructor
  · intro hconv x hx z
    rw [hS x hx z]
    set D : Set ℝ := {s : ℝ | x + s • z ∈ C} with hD
    have h0 : (0:ℝ) ∈ D := by simp [hD, hx]
    have hDc : Convex ℝ D := by
      intro s hs u hu p q hp hq hpq
      have := hCconv hs hu hp hq hpq
      simp only [hD, Set.mem_setOf_eq]
      convert this using 1
      have : p = 1 - q := by linarith
      subst this
      module
    have hg : ConvexOn ℝ D (fun s : ℝ => f (x + s • z)) := by
      refine ⟨hDc, ?_⟩
      intro s hs u hu p q hp hq hpq
      have := hconv.2 hs hu hp hq hpq
      have e : x + (p • s + q • u) • z = p • (x + s • z) + q • (x + u • z) := by
        have : p = 1 - q := by linarith
        subst this
        simp only [smul_eq_mul]
        module
      simp only [smul_eq_mul] at this ⊢
      rw [show x + (p * s + q * u) • z = p • (x + s • z) + q • (x + u • z) from by
        simpa using e]
      exact this
    have hmono := hg.monotoneOn_deriv (fun s hs => (key x z s hs).1.differentiableAt)
    have hφ : MonotoneOn (fun s : ℝ => fderiv ℝ f (x + s • z) z) D := by
      intro a ha b hb h
      have h1 := (key x z a ha).1.deriv
      have h2 := (key x z b hb).1.deriv
      simp only [] at h1 h2 ⊢
      rw [← h1, ← h2]
      exact hmono ha hb h
    have := hφ.derivWithin_nonneg (x := 0)
    rw [derivWithin_of_isOpen (hopen x z) h0] at this
    have k := (key x z 0 (by simpa using hx)).2.deriv
    simp only [zero_smul, add_zero] at k
    rw [← k]
    exact this
  · intro H
    refine ⟨hCconv, ?_⟩
    intro a ha b hb p q hp hq hpq
    have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, a + s • (b - a) ∈ C := by
      intro s hs
      have := hCconv ha hb (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1 (by ring)
      convert this using 1
      module
    have hgc : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun s : ℝ => f (a + s • (b - a))) := by
      apply convexOn_of_deriv2_nonneg (convex_Icc 0 1)
      · intro s hs
        exact (key a (b - a) s (hmem s hs)).1.continuousAt.continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact (key a (b - a) s (hmem s (Set.Ioo_subset_Icc_self hs))).1.differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hs' := hmem s (Set.Ioo_subset_Icc_self hs)
        have hev : (deriv fun s : ℝ => f (a + s • (b - a))) =ᶠ[nhds s]
            (fun s : ℝ => fderiv ℝ f (a + s • (b - a)) (b - a)) := by
          filter_upwards [(hopen a (b - a)).mem_nhds hs'] with u hu
          exact (key a (b - a) u hu).1.deriv
        exact ((key a (b - a) s hs').2.congr_of_eventuallyEq hev).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hs' := hmem s (Set.Ioo_subset_Icc_self hs)
        have hev : (deriv fun s : ℝ => f (a + s • (b - a))) =ᶠ[nhds s]
            (fun s : ℝ => fderiv ℝ f (a + s • (b - a)) (b - a)) := by
          filter_upwards [(hopen a (b - a)).mem_nhds hs'] with u hu
          exact (key a (b - a) u hu).1.deriv
        have := ((key a (b - a) s hs').2.congr_of_eventuallyEq hev).deriv
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
        rw [this, ← hS _ hs']
        exact H _ hs' _
    have := hgc.2 (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ hp hq hpq
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, zero_smul, add_zero, one_smul] at this
    have e : p • a + q • b = a + q • (b - a) := by
      have : p = 1 - q := by linarith
      subst this
      module
    rw [e]
    simpa using this

end «CAM-Bench-579»
