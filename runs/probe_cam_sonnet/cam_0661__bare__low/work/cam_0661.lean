import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-661»

structure PairedResidualMinimizationProblem where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  φ : ℝ → ℝ

def PairedResidualMinimizationProblem.residual
    (p : PairedResidualMinimizationProblem) (x : Fin p.n → ℝ) : Fin p.m → ℝ :=
  fun i => (∑ j : Fin p.n, p.A i j * x j) - p.b i

def PairedResidualMinimizationProblem.l1ObjectiveFn
    (p : PairedResidualMinimizationProblem) (x : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.m, |p.residual x i|

def PairedResidualMinimizationProblem.separableObjectiveFn
    (p : PairedResidualMinimizationProblem) (x : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.m, p.φ (p.residual x i)

abbrev PairedResidualMinimizationProblem.l1Objective :=
  PairedResidualMinimizationProblem.l1ObjectiveFn

abbrev PairedResidualMinimizationProblem.separableObjective :=
  PairedResidualMinimizationProblem.separableObjectiveFn
theorem l1_objective_of_separable_optimal_le
    (p : PairedResidualMinimizationProblem)
    (ε : ℝ)
    (hε : 0 < ε)
    (hRank : LinearIndependent ℝ (fun j : Fin p.n => fun i : Fin p.m => p.A i j))
    (hφ : p.φ = fun u : ℝ => Real.sqrt (u ^ 2 + ε))
    (xhat : Fin p.n → ℝ)
    (hxhat_opt : ∀ x : Fin p.n → ℝ, p.separableObjective xhat ≤ p.separableObjective x)
    (pstar : ℝ)
    (xstar : Fin p.n → ℝ)
    (hxstar_opt : ∀ x : Fin p.n → ℝ, p.l1Objective xstar ≤ p.l1Objective x)
    (hpstar : pstar = p.l1Objective xstar) :
    p.l1Objective xhat ≤
      pstar +
        ∑ i : Fin p.m,
          |p.residual xhat i| *
            (1 -
              |p.residual xhat i| /
                Real.sqrt ((p.residual xhat i) ^ 2 + ε)) := by

  simp only [PairedResidualMinimizationProblem.separableObjective, PairedResidualMinimizationProblem.separableObjectiveFn, hφ] at hxhat_opt
  set r := p.residual xhat with hr
  set q := p.residual xstar with hq
  have hres : ∀ t : ℝ, p.residual (xhat + t • (xstar - xhat)) = fun i => r i + t * (q i - r i) := by
    intro t; funext i
    have : ∑ j, p.A i j * (xhat + t • (xstar - xhat)) j = (1 - t) * ∑ j, p.A i j * xhat j + t * ∑ j, p.A i j * xstar j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; simp; ring
    simp only [PairedResidualMinimizationProblem.residual, hr, hq, this]
    ring
  have hpos : ∀ i, 0 < Real.sqrt (r i ^ 2 + ε) := fun i => Real.sqrt_pos.2 (by positivity)
  let g : ℝ → ℝ := fun t => ∑ i : Fin p.m, Real.sqrt ((r i + t * (q i - r i)) ^ 2 + ε)
  have hmin : IsLocalMin g 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have := hxhat_opt (xhat + t • (xstar - xhat))
    simp only [hres] at this
    simpa [g, hr] using this
  have hd : HasDerivAt g (∑ i : Fin p.m, (2 * (r i + 0 * (q i - r i)) * (q i - r i)) / (2 * Real.sqrt ((r i + 0 * (q i - r i)) ^ 2 + ε))) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have h1 : HasDerivAt (fun t : ℝ => (r i + t * (q i - r i)) ^ 2 + ε) (2 * (r i + 0 * (q i - r i)) * (q i - r i)) 0 := by
      have := (((hasDerivAt_id (0:ℝ)).mul_const (q i - r i)).const_add (r i)).pow 2
      simpa using this.add_const ε
    have h2 := h1.sqrt (by simp; positivity)
    exact h2
  have h0 := hmin.hasDerivAt_eq_zero hd
  simp only [zero_mul, add_zero] at h0
  have key : ∑ i, r i * (q i - r i) / Real.sqrt (r i ^ 2 + ε) = 0 := by
    rw [← h0]; apply Finset.sum_congr rfl; intro i _; field_simp [(hpos i).ne']
  have e2 : ∑ i, r i * r i / Real.sqrt (r i ^ 2 + ε) = ∑ i, r i * q i / Real.sqrt (r i ^ 2 + ε) := by
    have : ∑ i, (r i * q i / Real.sqrt (r i ^ 2 + ε) - r i * r i / Real.sqrt (r i ^ 2 + ε)) = 0 := by
      rw [← key]; apply Finset.sum_congr rfl; intro j _; ring
    rw [Finset.sum_sub_distrib] at this; linarith
  have hle : ∑ i, r i * q i / Real.sqrt (r i ^ 2 + ε) ≤ ∑ i, |q i| := by
    apply Finset.sum_le_sum; intro i _
    have hs := hpos i
    have h1 : |r i| ≤ Real.sqrt (r i ^ 2 + ε) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    rw [div_le_iff₀ hs]
    calc r i * q i ≤ |r i * q i| := le_abs_self _
      _ = |r i| * |q i| := abs_mul _ _
      _ ≤ Real.sqrt (r i ^ 2 + ε) * |q i| := by gcongr
      _ = _ := by ring
  have hsum : ∑ i, |r i| = ∑ i, |r i| * (1 - |r i| / Real.sqrt (r i ^ 2 + ε)) + ∑ i, r i * r i / Real.sqrt (r i ^ 2 + ε) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
    have := (hpos i).ne'
    have h : r i * r i = |r i| * |r i| := (abs_mul_abs_self _).symm
    rw [h]; field_simp; ring
  have : p.l1Objective xhat = ∑ i, |r i| := rfl
  have h2 : pstar = ∑ i, |q i| := hpstar
  rw [this, hsum]; linarith

end «CAM-Bench-661»
