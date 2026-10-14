import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-339»

def IndependentIdenticallyDistributed {m : ℕ} {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : MeasureTheory.Measure Ω) (v : Fin m → Ω → S) : Prop :=
  ProbabilityTheory.iIndepFun v μ ∧
    ∃ P : MeasureTheory.Measure S, MeasureTheory.IsProbabilityMeasure P ∧
      (∀ i : Fin m, Measurable (v i)) ∧
      ∀ i : Fin m, MeasureTheory.Measure.map (v i) μ = P

def IsProbabilityDensityFunction (p : ℝ → ENNReal) : Prop :=
  Measurable p ∧ (∫⁻ z : ℝ, p z) = 1

def IsLogConcave {n : ℕ} (f : (Fin n → ℝ) → ENNReal) : Prop :=
  Convex ℝ (Function.support f) ∧
    ∀ ⦃x y : Fin n → ℝ⦄,
      x ∈ Function.support f →
      y ∈ Function.support f →
      ∀ ⦃θ : ℝ⦄, θ ∈ Set.Icc (0 : ℝ) 1 →
        f (θ • x + (1 - θ) • y) ≥
          ENNReal.rpow (f x) θ * ENNReal.rpow (f y) (1 - θ)

def EffectiveDomain {n : ℕ} (g : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | g x < ⊤}

def LogLikelihood (L : α → ℝ) : α → EReal :=
  fun θ => if 0 < L θ then (Real.log (L θ) : EReal) else ⊤

structure LogConcaveLocationScaleMLE where
  n : ℕ
  m : ℕ
  y : Fin m → ℝ
  a : Fin m → Fin n → ℝ
  g : ℝ → EReal

def LogConcaveLocationScaleMLE.objective
    (p : LogConcaveLocationScaleMLE) (x : Fin p.n → ℝ) (μ σ : ℝ) : EReal :=
  (p.m : EReal) * Real.log σ +
    ∑ i : Fin p.m, p.g (((p.y i) - (∑ j : Fin p.n, p.a i j * x j) - μ) / σ)

def LogConcaveLocationScaleMLE.is_feasible
    (_p : LogConcaveLocationScaleMLE) (_x : Fin _p.n → ℝ) (_μ σ : ℝ) : Prop :=
  0 < σ

def LogConcaveLocationScaleMLE.residual
    (p : LogConcaveLocationScaleMLE) (x : Fin p.n → ℝ) (μ σ : ℝ) (i : Fin p.m) : ℝ :=
  ((p.y i) - (∑ j : Fin p.n, p.a i j * x j) - μ) / σ

theorem logConcaveLocationScaleMLE_equiv_and_convex
    (p : LogConcaveLocationScaleMLE)
    (f : ℝ → ENNReal)
    (hm : 1 ≤ p.m)
    (hf_pdf : IsProbabilityDensityFunction f)
    (hf_logconcave : IsLogConcave (n := 1) (fun x : Fin 1 → ℝ => f (x 0)))
    (hg : p.g = fun t => if 0 < (f t).toReal then (-Real.log ((f t).toReal) : EReal) else ⊤) :
    ((∀ x x' : Fin p.n → ℝ, ∀ μ μ' σ σ' : ℝ,
        p.is_feasible x μ σ →
        p.is_feasible x' μ' σ' →
        (LogLikelihood
            (fun u : (Fin p.n → ℝ) × ℝ × ℝ =>
              Real.exp
                (-((EReal.toReal (p.objective u.1 u.2.1 u.2.2)) : ℝ))))
            (x, μ, σ) ≥
          (LogLikelihood
            (fun u : (Fin p.n → ℝ) × ℝ × ℝ =>
              Real.exp
                (-((EReal.toReal (p.objective u.1 u.2.1 u.2.2)) : ℝ))))
            (x', μ', σ') ↔
        p.objective x μ σ ≤ p.objective x' μ' σ')) ∧
    ConvexOn ℝ
      {u : (Fin p.n → ℝ) × ℝ × ℝ | p.is_feasible u.1 u.2.1 u.2.2}
      (fun u : (Fin p.n → ℝ) × ℝ × ℝ =>
        EReal.toReal (p.objective u.1 u.2.1 u.2.2)) := by
  sorry

end «CAM-Bench-339»
