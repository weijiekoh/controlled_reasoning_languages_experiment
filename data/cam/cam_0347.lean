import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-347»

def logLikelihood {α Θ : Type*} (p : Θ → α → ℝ) (θ : Θ) (x : Fin K → α)
    (hpos : ∀ i : Fin K, 0 < p θ (x i)) : ℝ :=
  ∑ i : Fin K, Real.log (p θ (x i))

def IID {K : ℕ} {Ω α : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasurableSpace α]
    (X : Fin K → Ω → α) (P : MeasureTheory.Measure α) : Prop :=
  ProbabilityTheory.iIndepFun X μ ∧
    ∀ i : Fin K, AEMeasurable (X i) μ ∧ MeasureTheory.Measure.map (X i) μ = P

def normalizingFactor {Θ D : Type*}
    (totalMass : (D → ℝ) → ℝ) (q : Θ → D → ℝ) (θ : Θ)
    (hq_nonneg : ∀ x : D, 0 ≤ q θ x) : Set ℝ :=
  {a : ℝ | 0 < a ∧ totalMass (fun x => a * q θ x) = 1}

def expectation {Θ D E : Type*} [SMul ℝ E]
    (expectOp : (D → E) → E) (p : Θ → D → ℝ) (c : D → E)
    (h_law : ∀ θ : Θ, Prop) (θ : Θ) (h_integrable : Prop) : E :=
  expectOp (fun x => (p θ x) • c x)

theorem exponential_family_logLikelihood_gradient_average
    {K n : ℕ} {D : Type*}
    (θ : EuclideanSpace ℝ (Fin n))
    (x : Fin K → D)
    (c : D → EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : EuclideanSpace ℝ (Fin n) → D → ℝ)

    (expectOp : (D → EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n))
    (scalarExpectOp : (D → ℝ) → ℝ)
    (hK : 1 ≤ K)

    (hp : ∀ θ' : EuclideanSpace ℝ (Fin n), ∀ y : D,
        p θ' y = a θ' * Real.exp ⟪θ', c y⟫)

    (ha_normalizing : ∀ θ' : EuclideanSpace ℝ (Fin n),
        0 < a θ' ∧ a θ' * scalarExpectOp (fun x => Real.exp ⟪θ', c x⟫) = 1)

    (hexp_c : expectOp (fun y => p θ y • c y) =
        expectOp (fun y => (a θ * Real.exp ⟪θ, c y⟫) • c y))
    (hpos : ∀ i : Fin K, 0 < p θ (x i))
    (hdiff_a : DifferentiableAt ℝ (fun θ' => Real.log (a θ')) θ)
    (hdiff_ll :
      DifferentiableAt ℝ
        (fun θ' => ∑ i : Fin K, Real.log (p θ' (x i)))
        θ) :
    ((1 : ℝ) / (K : ℝ)) •
        gradient
          (fun θ' => ∑ i : Fin K, Real.log (p θ' (x i)))
          θ =
      (((1 : ℝ) / (K : ℝ)) • (∑ i : Fin K, c (x i))) -
        expectOp (fun y => p θ y • c y) := by
  sorry

end «CAM-Bench-347»
