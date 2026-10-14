import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-343»

open scoped Matrix

def GaussianDensity (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) (S : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x =>
    (2 * Real.pi) ^ (-(n : ℤ) / 2 : ℝ) *
      Real.sqrt (S.det)⁻¹ *
      Real.exp
        (-(1 / 2 : ℝ) *
          dotProduct (x - a) (fun i => ∑ j, (S⁻¹ i j) * (x - a) j))

def IndependentSamples {N : ℕ} {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (P : MeasureTheory.Measure α) (μ : MeasureTheory.Measure Ω) (y : Fin N → Ω → α) : Prop :=
  ProbabilityTheory.iIndepFun y μ ∧
    ∀ k : Fin N, MeasureTheory.Measure.map (y k) μ = P

def ConditionalCovarianceMatrix {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → EuclideanSpace ℝ (Fin n)) (W : Ω → Ω)
    (condExp :
      (Ω → Matrix (Fin n) (Fin n) ℝ) → Ω → Matrix (Fin n) (Fin n) ℝ)
    (condMean :
      (Ω → EuclideanSpace ℝ (Fin n)) → Ω → EuclideanSpace ℝ (Fin n))
    (_h_second_moment : ∀ _i _j : Fin n, ∃ bound : ℝ,
      0 ≤ bound) :
    Ω → Matrix (Fin n) (Fin n) ℝ :=
  fun ω =>
    condExp
      (fun ω' =>
        Matrix.of
          (fun i j =>
            (Z ω' i - condMean Z ω' i) * (Z ω' j - condMean Z ω' j)))
      (W ω)

def MaximumLikelihoodEstimator {Θ α : Type*} (feasible : Set Θ) (p : Θ → α → ℝ)
    {N : ℕ} (y : Fin N → α) : Set Θ :=
  {θ | θ ∈ feasible ∧ ∀ θ' ∈ feasible, ∏ k, p θ' (y k) ≤ ∏ k, p θ (y k)}

structure SparsePrecisionMatrixEstimation (n : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  sparsityPattern : Set (Fin n × Fin n)
  K : Matrix (Fin n) (Fin n) ℝ

def SparsePrecisionMatrixEstimation.is_feasible {n : ℕ}
    (p : SparsePrecisionMatrixEstimation n) : Prop :=
  p.K.PosDef ∧ ∀ ij : Fin n × Fin n, ij ∈ p.sparsityPattern → p.K ij.1 ij.2 = 0

def SparsePrecisionMatrixEstimation.objective {n : ℕ}
    (p : SparsePrecisionMatrixEstimation n) : ℝ :=
  -Real.log p.K.det + Matrix.trace (p.C * p.K)

theorem mle_gaussian_conditional_independence_equiv_sparse_precision
    {n N : ℕ}
    (hN : 1 ≤ N)
    (y : Fin N → EuclideanSpace ℝ (Fin n))
    (bar_y : EuclideanSpace ℝ (Fin n))
    (C : Matrix (Fin n) (Fin n) ℝ)
    (𝒩 : Set (Fin n × Fin n))
    (hbar_y : bar_y = (N : ℝ)⁻¹ • ∑ k, y k)
    (hC :
      C =
        (N : ℝ)⁻¹ •
          Matrix.of
            (fun i j =>
              ∑ k, ((y k i - bar_y i) * (y k j - bar_y j))))
    (P : SparsePrecisionMatrixEstimation n)
    (hP_C : P.C = C)
    (hP_pattern : P.sparsityPattern = 𝒩) :

    P.K ∈
        MaximumLikelihoodEstimator
          {K : Matrix (Fin n) (Fin n) ℝ | K.PosDef ∧ ∀ ij : Fin n × Fin n, ij ∈ 𝒩 → K ij.1 ij.2 = 0}
          (fun K x => GaussianDensity n bar_y K⁻¹ x)
          y ↔
      P.is_feasible ∧
      ∀ K' : Matrix (Fin n) (Fin n) ℝ,
        K'.PosDef →
        (∀ ij : Fin n × Fin n, ij ∈ 𝒩 → K' ij.1 ij.2 = 0) →
        P.objective ≤ -Real.log K'.det + Matrix.trace (C * K') := by
  sorry

end «CAM-Bench-343»
