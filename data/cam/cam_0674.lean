import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-674»

def IsTimeHomogeneousMarkovChain {Ω S : Type*} [Fintype S] [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (y : ℕ → Ω → S) : Prop :=
  ∃ P : Matrix S S ℝ,
    ∀ (t : ℕ) (ht : 1 ≤ t) (i j : S) (history : Fin (t - 1) → S),
      let nextEvent : Set Ω := {ω | y (t + 1) ω = i}
      let presentEvent : Set Ω := {ω | y t ω = j}
      let historyEvent : Set Ω := {ω | ∀ k : Fin (t - 1), y (k.1 + 1) ω = history k}
      0 < (μ (presentEvent ∩ historyEvent)).toReal →
        0 < (μ presentEvent).toReal →
          ((μ (nextEvent ∩ (presentEvent ∩ historyEvent))).toReal /
              (μ (presentEvent ∩ historyEvent)).toReal = P i j) ∧
            ((μ (nextEvent ∩ presentEvent)).toReal /
              (μ presentEvent).toReal = P i j)

def TransitionMatrix (n : ℕ) (condProb : Fin n → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ → Prop :=
  fun P => ∀ i j : Fin n, P i j = condProb i j

def IsColumnStochastic (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ j, (∑ i : Fin n, P i j) = 1

def LikelihoodFunction {Θ Ω : Type*} [MeasurableSpace Ω]
    (observedData : Set Ω) (Pr : Θ → MeasureTheory.Measure Ω) :
    Θ → ENNReal :=
  fun θ => Pr θ observedData

def IsMaximumLikelihoodEstimate {Θ : Type*} (feasible : Set Θ) (L : Θ → ℝ) (θHat : Θ) : Prop :=
  θHat ∈ feasible ∧ ∀ θ ∈ feasible, L θ ≤ L θHat

def IsProbabilityVector (n : ℕ) (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i : Fin n, p i) = 1

theorem mle_transition_matrix_empirical_frequencies
    (n N : ℕ) (hN : 1 ≤ N) (k : Fin N → Fin n) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      IsMaximumLikelihoodEstimate
        {Q : Matrix (Fin n) (Fin n) ℝ | IsColumnStochastic n Q}
        (fun Q =>
          ∏ t : Fin N,
            if h : t.1 + 1 < N then
              Q (k ⟨t.1 + 1, h⟩) (k t)
            else
              1)
        P ∧
      (∀ j : Fin n,
        0 <
          ((Finset.univ.filter fun t : Fin N =>
              if h : t.1 + 1 < N then
                k t = j
              else
                False).card) →
        ∀ i : Fin n,
          P i j =
            (((Finset.univ.filter fun t : Fin N =>
                if h : t.1 + 1 < N then
                  k t = j ∧ k ⟨t.1 + 1, h⟩ = i
                else
                  False).card) : ℝ) /
            (((Finset.univ.filter fun t : Fin N =>
                if h : t.1 + 1 < N then
                  k t = j
                else
                  False).card) : ℝ)) ∧
      (∀ j : Fin n,
        ((Finset.univ.filter fun t : Fin N =>
            if h : t.1 + 1 < N then
              k t = j
            else
              False).card) = 0 →
        ∀ p : Fin n → ℝ,
          IsProbabilityVector n p →
          ∃ P' : Matrix (Fin n) (Fin n) ℝ,
            IsMaximumLikelihoodEstimate
              {Q : Matrix (Fin n) (Fin n) ℝ | IsColumnStochastic n Q}
              (fun Q =>
                ∏ t : Fin N,
                  if h : t.1 + 1 < N then
                    Q (k ⟨t.1 + 1, h⟩) (k t)
                  else
                    1)
              P' ∧
            ∀ i : Fin n, P' i j = p i) := by
  sorry

end «CAM-Bench-674»
