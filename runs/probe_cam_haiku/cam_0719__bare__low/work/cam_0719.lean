import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

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
  have key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ), ContDiff ℝ 2 F →
      (ConvexOn ℝ Set.univ F ↔ ∀ x v : E, 0 ≤ fderiv ℝ (fun y => fderiv ℝ F y v) x v) := by
    intro E _ _ F hF
    have hd1 : Differentiable ℝ F := hF.differentiable (by norm_num)
    have hd2 : Differentiable ℝ (fderiv ℝ F) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hG : ∀ v : E, Differentiable ℝ (fun y => fderiv ℝ F y v) :=
      fun v y => (hd2 y).clm_apply (differentiableAt_const v)
    have L1 : ∀ x v : E, ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => F (x + s • v)) (fderiv ℝ F (x + t • v) v) t := by
      intro x v t
      have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      have := (hd1 (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl
      exact this
    have L2 : ∀ x v : E, ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => fderiv ℝ F (x + s • v) v)
          (fderiv ℝ (fun y => fderiv ℝ F y v) (x + t • v) v) t := by
      intro x v t
      have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      have := (hG v (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl
      exact this
    have hdl : ∀ x v : E, deriv (fun s : ℝ => F (x + s • v)) = fun t => fderiv ℝ F (x + t • v) v :=
      fun x v => funext fun t => (L1 x v t).deriv
    have hdiag : ∀ x v : E, ∀ t : ℝ,
        deriv (deriv (fun s : ℝ => F (x + s • v))) t
          = fderiv ℝ (fun y => fderiv ℝ F y v) (x + t • v) v := by
      intro x v t
      rw [hdl x v]
      exact (L2 x v t).deriv
    constructor
    · intro hc x v
      have hgc : ConvexOn ℝ Set.univ (fun s : ℝ => F (x + s • v)) := by
        refine ⟨convex_univ, ?_⟩
        intro a _ b _ c d hc0 hd0 hcd
        have := hc.2 (Set.mem_univ (x + a • v)) (Set.mem_univ (x + b • v)) hc0 hd0 hcd
        have e : c • (x + a • v) + d • (x + b • v) = x + (c • a + d • b) • v := by
          rw [show c = 1 - d by linarith]; module
        show F (x + (c • a + d • b) • v) ≤ c • F (x + a • v) + d • F (x + b • v)
        rw [← e]
        exact this
      have hdiff : Differentiable ℝ (fun s : ℝ => F (x + s • v)) :=
        fun t => (L1 x v t).differentiableAt
      have hgm : Monotone (deriv (fun s : ℝ => F (x + s • v))) := by
        intro a b hab
        exact hgc.monotoneOn_deriv (fun t _ => hdiff t) (Set.mem_univ a) (Set.mem_univ b) hab
      have h2 : 0 ≤ deriv (deriv (fun s : ℝ => F (x + s • v))) 0 := hgm.deriv_nonneg
      have h3 := hdiag x v 0
      simp only [zero_smul, add_zero] at h3
      rw [← h3]
      exact h2
    · intro hQ
      constructor
      · exact convex_univ
      intro x _ y _ a b ha hb hab
      have hdiff : Differentiable ℝ (fun s : ℝ => F (x + s • (y - x))) :=
        fun t => (L1 x (y - x) t).differentiableAt
      have hdd : Differentiable ℝ (deriv (fun s : ℝ => F (x + s • (y - x)))) := by
        rw [hdl x (y - x)]
        exact fun t => (L2 x (y - x) t).differentiableAt
      have hc : ConvexOn ℝ Set.univ (fun s : ℝ => F (x + s • (y - x))) := by
        refine convexOn_univ_of_deriv2_nonneg hdiff hdd (fun t => ?_)
        show 0 ≤ deriv (deriv (fun s : ℝ => F (x + s • (y - x)))) t
        rw [hdiag]
        exact hQ _ _
      have h := hc.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ)) ha hb hab
      have e1 : x + (a • (0:ℝ) + b • (1:ℝ)) • (y - x) = a • x + b • y := by
        rw [show a = 1 - b by linarith]; module
      have e2 : x + (0:ℝ) • (y - x) = x := by simp
      have e3 : x + (1:ℝ) • (y - x) = y := by simp
      beta_reduce at h
      rw [e1, e2, e3] at h
      exact h
  have hneg : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ), ContDiff ℝ 2 F →
      (ConcaveOn ℝ Set.univ F ↔ ∀ x v : E, fderiv ℝ (fun y => fderiv ℝ F y v) x v ≤ 0) := by
    intro E _ _ F hF
    have hk := key E (-F) hF.neg
    have hn : ∀ x v : E, fderiv ℝ (fun y => fderiv ℝ (-F) y v) x v
        = -fderiv ℝ (fun y => fderiv ℝ F y v) x v := by
      intro x v
      simp [fderiv_neg]
    rw [← neg_convexOn_iff, hk]
    simp only [hn, neg_nonneg]
  have hcontx : ∀ z : EuclideanSpace ℝ (Fin m), ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)) :=
    fun z => hf.comp (contDiff_id.prodMk contDiff_const)
  have hcontz : ∀ x : EuclideanSpace ℝ (Fin n), ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)) :=
    fun x => hf.comp (contDiff_const.prodMk contDiff_id)
  constructor
  · rintro ⟨h1, h2⟩ p
    exact ⟨fun v => (key _ _ (hcontx p.2)).1 (h1 p.2) p.1 v,
      fun w => (hneg _ _ (hcontz p.1)).1 (h2 p.1) p.2 w⟩
  · intro h
    exact ⟨fun z => (key _ _ (hcontx z)).2 (fun x v => (h (x, z)).1 v),
      fun x => (hneg _ _ (hcontz x)).2 (fun z w => (h (x, z)).2 w)⟩

end «CAM-Bench-719»
