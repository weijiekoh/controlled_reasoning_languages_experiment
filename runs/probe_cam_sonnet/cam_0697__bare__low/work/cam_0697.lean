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
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨c0, hc0⟩ := hC_nonempty
  obtain ⟨d0, hd0⟩ := hD_nonempty
  have hne : ∀ z : EuclideanSpace ℝ (Fin n), {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - (z + d)‖}.Nonempty :=
    fun z => ⟨_, c0, hc0, d0, hd0, rfl⟩
  have hbdd : ∀ z : EuclideanSpace ℝ (Fin n), BddBelow {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - (z + d)‖} := by
    intro z; refine ⟨0, ?_⟩; rintro r ⟨c, _, d, _, rfl⟩; exact norm_nonneg _
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r1, ⟨c1, hc1, d1, hd1, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (hne x)
    (show sInf {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - (x + d)‖} < _ + ε from lt_add_of_pos_right _ hε)
  obtain ⟨r2, ⟨c2, hc2, d2, hd2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (hne y)
    (show sInf {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - (y + d)‖} < _ + ε from lt_add_of_pos_right _ hε)
  have hmem : ‖(a • c1 + b • c2) - ((a • x + b • y) + (a • d1 + b • d2))‖ ∈ {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - ((a • x + b • y) + d)‖} :=
    ⟨_, hC_convex hc1 hc2 ha hb hab, _, hD_convex hd1 hd2 ha hb hab, rfl⟩
  have hle := csInf_le (hbdd _) hmem
  have heq : (a • c1 + b • c2) - ((a • x + b • y) + (a • d1 + b • d2)) = a • (c1 - (x + d1)) + b • (c2 - (y + d2)) := by
    simp only [smul_sub, smul_add]; abel
  rw [heq] at hle
  have h3 := norm_add_le (a • (c1 - (x + d1))) (b • (c2 - (y + d2)))
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] at h3
  nlinarith [mul_le_mul_of_nonneg_left h1.le ha, mul_le_mul_of_nonneg_left h2.le hb]

end «CAM-Bench-697»
