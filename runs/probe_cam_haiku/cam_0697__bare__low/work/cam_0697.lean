import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-697»

open scoped BigOperators

theorem dist_C_translate_add_convex
    {n : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D) :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        sInf {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - (x + d)‖}) := by
  classical
  set S : EuclideanSpace ℝ (Fin n) → Set ℝ :=
    fun x => {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - (x + d)‖} with hS
  have hne : ∀ x, (S x).Nonempty := by
    intro x
    obtain ⟨c, hc⟩ := hC_nonempty
    obtain ⟨d, hd⟩ := hD_nonempty
    exact ⟨_, c, hc, d, hd, rfl⟩
  have hbdd : ∀ x, BddBelow (S x) := by
    intro x
    refine ⟨0, ?_⟩
    rintro r ⟨c, _, d, _, rfl⟩
    exact norm_nonneg _
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  show sInf (S (a • x + b • y)) ≤ a * sInf (S x) + b * sInf (S y)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hx : sInf (S x) < sInf (S x) + ε / 2 := by linarith
  have hy : sInf (S y) < sInf (S y) + ε / 2 := by linarith
  obtain ⟨r1, ⟨c1, hc1, d1, hd1, rfl⟩, hr1⟩ := exists_lt_of_csInf_lt (hne x) hx
  obtain ⟨r2, ⟨c2, hc2, d2, hd2, rfl⟩, hr2⟩ := exists_lt_of_csInf_lt (hne y) hy
  have hmem : ‖(a • c1 + b • c2) - ((a • x + b • y) + (a • d1 + b • d2))‖
      ∈ S (a • x + b • y) :=
    ⟨_, hC_convex hc1 hc2 ha hb hab, _, hD_convex hd1 hd2 ha hb hab, rfl⟩
  have key : (a • c1 + b • c2) - ((a • x + b • y) + (a • d1 + b • d2))
      = a • (c1 - (x + d1)) + b • (c2 - (y + d2)) := by
    module
  have hnorm : ‖(a • c1 + b • c2) - ((a • x + b • y) + (a • d1 + b • d2))‖
      ≤ a * ‖c1 - (x + d1)‖ + b * ‖c2 - (y + d2)‖ := by
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h1 := csInf_le (hbdd _) hmem
  nlinarith [mul_le_mul_of_nonneg_left hr1.le ha, mul_le_mul_of_nonneg_left hr2.le hb]

end «CAM-Bench-697»
