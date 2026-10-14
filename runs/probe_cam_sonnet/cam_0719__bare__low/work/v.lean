import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators


theorem line_h1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x v : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

theorem line_d1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) (x v : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => h (x + t • v)) (fderiv ℝ h (x + t • v) v) t := by
  have hd : DifferentiableAt ℝ h (x + t • v) := (hh.differentiable (by norm_num)) _
  exact hd.hasFDerivAt.comp_hasDerivAt t (line_h1 x v t)

theorem line_d2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) (x v : E) (t : ℝ) :
    HasDerivAt (deriv (fun t : ℝ => h (x + t • v))) (fderiv ℝ (fun y => fderiv ℝ h y v) (x + t • v) v) t := by
  have hc : ContDiff ℝ 1 (fun y => fderiv ℝ h y v) := by
    have : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (by norm_num)
    exact this.clm_apply contDiff_const
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ h y v) (x + t • v) :=
    (hc.differentiable (by norm_num)) _
  have e : deriv (fun t : ℝ => h (x + t • v)) = fun t => fderiv ℝ h (x + t • v) v := by
    funext s; exact (line_d1 hh x v s).deriv
  rw [e]
  exact hd.hasFDerivAt.comp_hasDerivAt t (line_h1 x v t)

theorem convex_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) :
    ConvexOn ℝ Set.univ h ↔ ∀ x v, 0 ≤ fderiv ℝ (fun y => fderiv ℝ h y v) x v := by
  constructor
  · intro hc x v
    let A : ℝ →ᵃ[ℝ] E := ⟨fun t => x + t • v, (ContinuousLinearMap.toSpanSingleton ℝ v : ℝ →ₗ[ℝ] E), by
      intro p q; simp [add_smul]; abel⟩
    have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => h (x + t • v)) :=
      hc.comp_affineMap A
    have hm := hφ.monotoneOn_deriv (fun t _ => (line_d1 hh x v t).differentiableAt)
    have := Monotone.deriv_nonneg (x := 0) (fun a b hab => hm (Set.mem_univ a) (Set.mem_univ b) hab)
    have e := (line_d2 hh x v 0).deriv
    simp at e
    rw [e] at this
    exact this
  · intro H
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => h (x + t • (y - x))) := by
      apply convexOn_univ_of_deriv2_nonneg
      · intro t; exact (line_d1 hh x (y-x) t).differentiableAt
      · intro t
        have e : deriv (fun t : ℝ => h (x + t • (y - x))) = fun t => fderiv ℝ h (x + t • (y-x)) (y-x) := by
          funext s; exact (line_d1 hh x (y-x) s).deriv
        exact (line_d2 hh x (y-x) t).differentiableAt
      · intro t
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
        rw [(line_d2 hh x (y-x) t).deriv]
        exact H _ _
    have := hφ.2 (Set.mem_univ 0) (Set.mem_univ 1) ha hb hab
    simp at this
    have e : a • x + b • y = x + b • (y - x) := by
      have : a = 1 - b := by linarith
      subst this
      simp [smul_sub, sub_smul]; abel
    rw [e]
    simpa [smul_eq_mul] using this
theorem concave_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (hh : ContDiff ℝ 2 h) :
    ConcaveOn ℝ Set.univ h ↔ ∀ x v, fderiv ℝ (fun y => fderiv ℝ h y v) x v ≤ 0 := by
  rw [← neg_convexOn_iff]; change ConvexOn ℝ Set.univ (fun x => -h x) ↔ _; rw [convex_iff hh.neg]
  have e : ∀ v : E, (fun y => fderiv ℝ (fun z => -h z) y v) = fun y => -(fderiv ℝ h y v) := by
    intro v; funext y; rw [fderiv_fun_neg]; rfl
  simp only [Pi.neg_def, e]
  refine forall_congr' fun x => forall_congr' fun v => ?_
  rw [fderiv_fun_neg]
  simp

namespace «CAM-Bench-719»

theorem convexConcave_iff_hessian_blocks_semidefinite
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    ((
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    ) ↔
    (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      (∀ v : EuclideanSpace ℝ (Fin n),
        0 ≤
          (fderiv ℝ
            (fun x : EuclideanSpace ℝ (Fin n) =>
              (fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => f (x', p.2)) x) v)
            p.1) v) ∧
      (∀ w : EuclideanSpace ℝ (Fin m),
        (fderiv ℝ
          (fun z : EuclideanSpace ℝ (Fin m) =>
            (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin m) => f (p.1, z')) z) w)
          p.2) w ≤ 0)) := by
  have hx : ∀ z : EuclideanSpace ℝ (Fin m),
      ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)) := fun z =>
    hf.comp (contDiff_id.prodMk contDiff_const)
  have hz : ∀ x : EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)) := fun x =>
    hf.comp (contDiff_const.prodMk contDiff_id)
  constructor
  · rintro ⟨h1, h2⟩ p
    exact ⟨fun v => (convex_iff (hx p.2)).1 (h1 p.2) p.1 v,
      fun w => (concave_iff (hz p.1)).1 (h2 p.1) p.2 w⟩
  · intro H
    exact ⟨fun z => (convex_iff (hx z)).2 fun x v => (H (x, z)).1 v,
      fun x => (concave_iff (hz x)).2 fun z w => (H (x, z)).2 w⟩

end «CAM-Bench-719»
