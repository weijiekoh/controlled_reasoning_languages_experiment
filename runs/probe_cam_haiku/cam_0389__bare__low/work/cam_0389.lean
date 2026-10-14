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
  have key : ∀ (a b : Fin (N+1) → ℝ) (p q ω : ℝ),
      H (p • a + q • b) ω = p * H a ω + q * H b ω := by
    intro a b p q ω
    simp only [H, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have mono : ∀ x z : ℝ, x ∈ feasibleT → x ≤ z → z ≤ Real.pi → z ∈ feasibleT := by
    intro x z hx hxz hzπ
    obtain ⟨⟨hx0, hxπ⟩, a, ha⟩ := hx
    have ha' : a ∈ F x := ha
    simp only [F, Set.mem_setOf_eq] at ha'
    refine ⟨⟨le_trans hx0 hxz, hzπ⟩, a, ?_⟩
    simp only [F, Set.mem_setOf_eq]
    exact ⟨ha'.1, fun ω hω => ha'.2 ω ⟨le_trans hxz hω.1, hω.2⟩⟩
  constructor
  · intro t _ a ha b hb p q hp hq hpq
    have ha' : a ∈ F t := ha
    have hb' : b ∈ F t := hb
    simp only [F, Set.mem_setOf_eq] at ha' hb' ⊢
    obtain ⟨h1, h2⟩ := ha'
    obtain ⟨h3, h4⟩ := hb'
    refine ⟨fun ω hω => ?_, fun ω hω => ?_⟩
    · rw [key]
      obtain ⟨h5, h6⟩ := h1 ω hω
      obtain ⟨h7, h8⟩ := h3 ω hω
      constructor <;> nlinarith
    · rw [key]
      have e1 := h2 ω hω
      have e2 := h4 ω hω
      rw [abs_le] at e1 e2 ⊢
      constructor <;> nlinarith
  · intro s x hx y hy p q hp hq hpq
    obtain ⟨hxf, hxs⟩ := hx
    obtain ⟨hyf, hys⟩ := hy
    simp only [Set.mem_setOf_eq, id] at hxs hys ⊢
    have hm : min x y ∈ feasibleT := by
      rcases le_total x y with h | h
      · rw [min_eq_left h]; exact hxf
      · rw [min_eq_right h]; exact hyf
    have hz0 : 0 ≤ p * x + q * y := by
      have := hxf.1.1; have := hyf.1.1
      nlinarith
    have hzπ : p * x + q * y ≤ Real.pi := by
      have := hxf.1.2; have := hyf.1.2
      nlinarith
    have hmin : min x y ≤ p * x + q * y := by
      rcases le_total x y with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    have hmax : p * x + q * y ≤ max x y := by
      rcases le_total x y with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    refine ⟨mono _ _ hm hmin hzπ, ?_⟩
    exact le_trans hmax (max_le hxs hys)

end «CAM-Bench-389»
