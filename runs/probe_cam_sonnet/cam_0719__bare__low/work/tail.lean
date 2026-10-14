
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
