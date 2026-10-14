import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-341»

def IsMaximumAPosterioriEstimate (C : Set α) (posterior : α → ℝ) (xHat : α) : Prop :=
  xHat ∈ C ∧ ∀ x ∈ C, posterior x ≤ posterior xHat

def IsPriorDensity {α Ω : Type*} [MeasureTheory.MeasureSpace α] [MeasureTheory.MeasureSpace Ω]
    (μ : MeasureTheory.Measure Ω) (ν : MeasureTheory.Measure α)
    (C : Set α) (X : Ω → α) (pX : C → ℝ) : Prop :=
  by
    classical
    exact
      Measurable X ∧
      MeasurableSet C ∧
      (∀ ω, X ω ∈ C) ∧
      (∀ x : C, 0 ≤ pX x) ∧
      ∀ A : Set α, MeasurableSet A → A ⊆ C →
        (μ {ω | X ω ∈ A}).toReal =
          ∫ x in A, if hx : x ∈ C then pX ⟨x, hx⟩ else 0 ∂ν

def IsPosteriorDensity {α Ω Y : Type*} [MeasureTheory.MeasureSpace α] [MeasureTheory.MeasureSpace Ω]
    [MeasureTheory.MeasureSpace Y]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (ν : MeasureTheory.Measure α)
    (X : Ω → α) (Obs : Ω → Y)
    (condLaw : Y → MeasureTheory.Measure α)
    (hcond : condLaw = fun y =>
      MeasureTheory.Measure.map X (ProbabilityTheory.cond μ (Obs ⁻¹' ({y} : Set Y))))
    (y : Y) (posterior : α → ℝ) : Prop :=
  Measurable X ∧
  Measurable Obs ∧
  (∀ x, 0 ≤ posterior x) ∧
  ∀ A : Set α, MeasurableSet A →
    ((condLaw y) A).toReal = ∫ x in A, posterior x ∂ν

def argmax (C : Set α) (f : α → WithTop (WithBot ℝ)) : Set α :=
  {x | x ∈ C ∧ ∀ z ∈ C, f z ≤ f x}

def argmin (C : Set α) (f : α → WithTop (WithBot ℝ)) : Set α :=
  {x | x ∈ C ∧ ∀ z ∈ C, f x ≤ f z}

theorem map_estimate_iff_mem_argmin_phi
    (y1 y2 y3 : ℝ) (posterior : ℝ × ℝ → ℝ) (xHat : ℝ × ℝ)
    (hposterior :
      ∀ x : ℝ × ℝ,
        posterior x =
          Real.exp
            (-((1 / 2 : ℝ) *
                ((y1 - x.1) ^ 2 + (y2 - x.2) ^ 2 + (y3 - x.1 + x.2) ^ 2) +
              (x.1 + x.2)))) :
    IsMaximumAPosterioriEstimate
      {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2}
      posterior
      xHat
      ↔
    xHat ∈
      argmin
        {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2}
        (fun x =>
          show WithTop (WithBot ℝ) from
            (((1 / 2 : ℝ) *
                ((y1 - x.1) ^ 2 + (y2 - x.2) ^ 2 + (y3 - x.1 + x.2) ^ 2) +
              (x.1 + x.2) : ℝ) : WithBot ℝ)) := by
  sorry

end «CAM-Bench-341»
