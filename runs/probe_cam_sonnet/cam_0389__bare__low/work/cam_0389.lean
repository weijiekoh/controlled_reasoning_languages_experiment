import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-389»

def IsQuasiconvexOptimizationProblem
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (X : Set E) (f : E → ℝ) : Prop :=
  ∀ t : ℝ, Convex ℝ {x | x ∈ X ∧ f x ≤ t}

theorem feasibility_sets_convex_and_filter_problem_quasiconvex
    (N : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    let H : (Fin (N + 1) → ℝ) → ℝ → ℝ :=
      fun a ω => ∑ k : Fin (N + 1), a k * Real.cos ((k : ℝ) * ω)
    let F : ℝ → Set (Fin (N + 1) → ℝ) :=
      fun t =>
        {a | (∀ ω ∈ Set.Icc (0 : ℝ) (Real.pi / 3), 0.89 ≤ H a ω ∧ H a ω ≤ 1.12) ∧
             (∀ ω ∈ Set.Icc t Real.pi, |H a ω| ≤ α)}
    let feasibleT : Set ℝ :=
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧ (F t).Nonempty}
    (∀ t ∈ Set.Icc (0 : ℝ) Real.pi, Convex ℝ (F t)) ∧
      IsQuasiconvexOptimizationProblem
        feasibleT
        (fun t => t) := by
  intro H F feasibleT
  have hH : ∀ (a b : Fin (N + 1) → ℝ) (p q : ℝ) (ω : ℝ), H (p • a + q • b) ω = p * H a ω + q * H b ω := by
    intro a b p q ω
    simp only [H, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  constructor
  · intro t _ a ha b hb p q hp hq hpq
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨fun ω hω => ?_, fun ω hω => ?_⟩
    · rw [hH]
      constructor <;> nlinarith [ha1 ω hω, hb1 ω hω]
    · have h1 := ha2 ω hω
      have h2 := hb2 ω hω
      rw [hH]
      calc |p * H a ω + q * H b ω| ≤ |p * H a ω| + |q * H b ω| := abs_add_le _ _
        _ = p * |H a ω| + q * |H b ω| := by rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
        _ ≤ p * α + q * α := by gcongr
        _ = α := by rw [← add_mul, hpq, one_mul]
  · intro s t1 ht1 t2 ht2 p q hp hq hpq
    have mono : ∀ u v : ℝ, u ≤ v → (F u).Nonempty → (F v).Nonempty := by
      rintro u v huv ⟨a, ha1, ha2⟩
      exact ⟨a, ha1, fun ω hω => ha2 ω ⟨huv.trans hω.1, hω.2⟩⟩
    obtain ⟨⟨h1a, h1b⟩, h1c⟩ := ht1
    obtain ⟨⟨h2a, h2b⟩, h2c⟩ := ht2
    simp only [Set.mem_setOf_eq, feasibleT, Set.mem_Icc] at *
    rcases le_total t1 t2 with h | h
    · have e1 : t1 ≤ p • t1 + q • t2 := by simp only [smul_eq_mul]; nlinarith
      have e2 : p • t1 + q • t2 ≤ t2 := by simp only [smul_eq_mul]; nlinarith
      exact ⟨⟨⟨by linarith, by linarith⟩, mono _ _ e1 h1b⟩, by linarith⟩
    · have e1 : t2 ≤ p • t1 + q • t2 := by simp only [smul_eq_mul]; nlinarith
      have e2 : p • t1 + q • t2 ≤ t1 := by simp only [smul_eq_mul]; nlinarith
      exact ⟨⟨⟨by linarith, by linarith⟩, mono _ _ e1 h2b⟩, by linarith⟩

end «CAM-Bench-389»
