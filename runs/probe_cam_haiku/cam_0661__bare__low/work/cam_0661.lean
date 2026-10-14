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
  classical
  set r : Fin p.m → ℝ := fun i => p.residual xhat i with hr
  set s : Fin p.m → ℝ := fun i => p.residual xstar i with hs
  have hpos : ∀ i, 0 < (r i)^2 + ε := fun i => by positivity
  have hres : ∀ t : ℝ, ∀ i, p.residual (xhat + t • (xstar - xhat)) i = r i + t * (s i - r i) := by
    intro t i
    simp only [PairedResidualMinimizationProblem.residual, hr, hs, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    have key : ∑ j, p.A i j * (xhat j + t * (xstar j - xhat j))
        = ∑ j, p.A i j * xhat j + t * (∑ j, p.A i j * xstar j - ∑ j, p.A i j * xhat j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros; ring
    rw [key]; ring
  have hg : ∀ t : ℝ, p.separableObjective xhat ≤ p.separableObjective (xhat + t • (xstar - xhat)) :=
    fun t => hxhat_opt _
  have hgeq : ∀ t : ℝ, p.separableObjective (xhat + t • (xstar - xhat))
      = ∑ i, Real.sqrt ((r i + t * (s i - r i))^2 + ε) := by
    intro t
    simp only [PairedResidualMinimizationProblem.separableObjective, PairedResidualMinimizationProblem.separableObjectiveFn, hφ]
    simp only [hres]
  have hmin : IsLocalMin (fun t : ℝ => ∑ i, Real.sqrt ((r i + t * (s i - r i))^2 + ε)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h0 : p.separableObjective xhat = ∑ i, Real.sqrt ((r i + 0 * (s i - r i))^2 + ε) := by
      have := hgeq 0; rw [zero_smul, add_zero] at this; exact this.symm ▸ rfl
    show ∑ i, Real.sqrt ((r i + 0 * (s i - r i))^2 + ε) ≤ ∑ i, Real.sqrt ((r i + t * (s i - r i))^2 + ε)
    rw [← h0, ← hgeq t]
    exact hg t
  have aux : ∀ (a c : ℝ), HasDerivAt (fun t : ℝ => Real.sqrt ((a + t * c)^2 + ε))
      (c * a / Real.sqrt (a^2 + ε)) 0 := by
    intro a c
    have hl : HasDerivAt (fun t : ℝ => a + t * c) c 0 := by
      have := ((hasDerivAt_id' (0:ℝ)).mul_const c).const_add a
      simpa only [one_mul] using this
    have hsq : Real.sqrt (a^2 + ε) ≠ 0 := by
      have : 0 < a^2 + ε := by positivity
      exact (Real.sqrt_pos.mpr this).ne'
    refine (((hl.pow 2).add_const ε).sqrt ?_).congr_deriv ?_
    · show (a + (0:ℝ) * c)^2 + ε ≠ 0
      positivity
    · show (↑(2:ℕ) * (a + (0:ℝ) * c) ^ (2 - 1) * c) / (2 * Real.sqrt ((a + (0:ℝ) * c)^2 + ε)) = c * a / Real.sqrt (a^2 + ε)
      norm_num
      field_simp
  have hderiv := hmin.hasDerivAt_eq_zero (HasDerivAt.fun_sum (fun i _ => aux (r i) (s i - r i)))
  have hw : ∀ i, |r i / Real.sqrt ((r i)^2 + ε)| ≤ 1 := by
    intro i
    have hS : 0 < Real.sqrt ((r i)^2 + ε) := Real.sqrt_pos.mpr (hpos i)
    rw [abs_div, abs_of_pos hS, div_le_one hS]
    exact Real.abs_le_sqrt (le_add_of_nonneg_right hε.le)
  have hsum : ∑ i, r i * (r i / Real.sqrt ((r i)^2 + ε)) = ∑ i, s i * (r i / Real.sqrt ((r i)^2 + ε)) := by
    have : ∑ i, (s i - r i) * (r i / Real.sqrt ((r i)^2 + ε)) = 0 := by
      rw [← hderiv]; exact Finset.sum_congr rfl (fun i _ => by ring)
    have h3 : ∑ i, (s i - r i) * (r i / Real.sqrt ((r i)^2 + ε))
        = ∑ i, s i * (r i / Real.sqrt ((r i)^2 + ε)) - ∑ i, r i * (r i / Real.sqrt ((r i)^2 + ε)) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    linarith
  have hle : ∑ i, r i * (r i / Real.sqrt ((r i)^2 + ε)) ≤ ∑ i, |s i| := by
    rw [hsum]
    apply Finset.sum_le_sum
    intro i _
    calc s i * (r i / Real.sqrt ((r i)^2 + ε)) ≤ |s i * (r i / Real.sqrt ((r i)^2 + ε))| := le_abs_self _
      _ = |s i| * |r i / Real.sqrt ((r i)^2 + ε)| := abs_mul _ _
      _ ≤ |s i| * 1 := mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
      _ = |s i| := mul_one _
  have hterm : ∀ i, |r i| * (1 - |r i| / Real.sqrt ((r i)^2 + ε))
      = |r i| - r i * (r i / Real.sqrt ((r i)^2 + ε)) := by
    intro i
    have hsq : |r i| * |r i| = r i * r i := abs_mul_abs_self _
    have : |r i| * (|r i| / Real.sqrt ((r i)^2 + ε)) = r i * (r i / Real.sqrt ((r i)^2 + ε)) := by
      have e : |r i| * (|r i| / Real.sqrt ((r i)^2 + ε)) = (|r i| * |r i|) / Real.sqrt ((r i)^2 + ε) := by ring
      rw [e, hsq]; ring
    linarith
  have hpstar' : pstar = ∑ i, |s i| := by
    rw [hpstar]; rfl
  have hsumterm : ∑ i, |r i| * (1 - |r i| / Real.sqrt ((r i)^2 + ε))
      = ∑ i, |r i| - ∑ i, r i * (r i / Real.sqrt ((r i)^2 + ε)) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => hterm i)
  show ∑ i, |p.residual xhat i| ≤ pstar + ∑ i, |p.residual xhat i| * (1 - |p.residual xhat i| / Real.sqrt ((p.residual xhat i)^2 + ε))
  rw [hsumterm, hpstar']
  linarith

end «CAM-Bench-661»
