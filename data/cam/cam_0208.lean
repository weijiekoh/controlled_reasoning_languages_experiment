import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-208»

def lagrangian
    {X J K : Type*}
    [Fintype J]
    [Fintype K]
    (f : X → ℝ)
    (h : J → X → ℝ)
    (g : K → X → ℝ)
    (x : X)
    (lam : J → ℝ)
    (μ : K → ℝ) : ℝ :=
  f x + ∑ j, lam j * h j x + ∑ k, μ k * g k x

structure MultiPeriodEconomicDispatch
    (n T : ℕ) where
  d : Fin T → ℝ
  Pmin : Fin n → ℝ
  Pmax : Fin n → ℝ
  R : Fin n → ℝ
  α : Fin n → ℝ
  β : Fin n → ℝ
  γ : Fin n → ℝ
  hT : 1 ≤ T
  demand_pos : ∀ t, 0 < d t
  alpha_pos : ∀ i, 0 < α i
  beta_pos : ∀ i, 0 < β i
  gamma_pos : ∀ i, 0 < γ i
  feasible :
    ∃ q : Fin n → Fin T → ℝ,
      (∀ i t, 0 ≤ q i t) ∧
      (∀ t, ∑ i, q i t = d t) ∧
      (∀ i t, Pmin i ≤ q i t ∧ q i t ≤ Pmax i) ∧
      (∀ i (t : Fin (T - 1)),
        |q i (Fin.castLEOrderEmb (Nat.sub_le T 1) t) -
          q i (⟨t.1.succ, by
            have hT' : 0 < T := Nat.succ_le_iff.mp hT
            exact lt_of_le_of_lt (Nat.succ_le_of_lt t.2) (Nat.sub_lt hT' (by simp))⟩)| ≤ R i)

def nextPeriod {T : ℕ} (hT : 1 ≤ T) (t : Fin (T - 1)) : Fin T :=
  ⟨t.1.succ, by
    have hT' : 0 < T := Nat.succ_le_iff.mp hT
    exact lt_of_le_of_lt (Nat.succ_le_of_lt t.2) (Nat.sub_lt hT' (by simp))⟩

def MultiPeriodEconomicDispatch.phi
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (i : Fin n) (u : ℝ) : ℝ :=
  prob.α i * u + prob.β i * u^2

def MultiPeriodEconomicDispatch.psi
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (i : Fin n) (v : ℝ) : ℝ :=
  prob.γ i * |v|

def MultiPeriodEconomicDispatch.objective
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (q : Fin n → Fin T → ℝ) : ℝ :=
  (∑ i, ∑ t, prob.phi i (q i t)) +
    ∑ i, ∑ t : Fin (T - 1),
      prob.psi i
        (q i (Fin.castLEOrderEmb (Nat.sub_le T 1) t) - q i (nextPeriod prob.hT t))

def MultiPeriodEconomicDispatch.IsFeasible
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (q : Fin n → Fin T → ℝ) : Prop :=
  (∀ i t, 0 ≤ q i t) ∧
  (∀ t, ∑ i, q i t = prob.d t) ∧
  (∀ i t, prob.Pmin i ≤ q i t ∧ q i t ≤ prob.Pmax i) ∧
  (∀ i (t : Fin (T - 1)),
    |q i (Fin.castLEOrderEmb (Nat.sub_le T 1) t) -
      q i (nextPeriod prob.hT t)| ≤ prob.R i)

structure SingleGeneratorDispatchProblem (T : ℕ) where
  Q : Fin T → ℝ
  Pmin : ℝ
  Pmax : ℝ
  R : ℝ
  α : ℝ
  β : ℝ
  γ : ℝ
  hT : 1 ≤ T
  alpha_pos : 0 < α
  beta_pos : 0 < β
  gamma_pos : 0 < γ

def SingleGeneratorDispatchProblem.objective
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) (q : Fin T → ℝ) : ℝ :=
  (∑ t, ((prob.α * q t + prob.β * (q t)^2) - prob.Q t * q t)) +
    ∑ t : Fin (T - 1),
      prob.γ * |q (nextPeriod prob.hT t) - q (Fin.castLEOrderEmb (Nat.sub_le T 1) t)|

def SingleGeneratorDispatchProblem.IsFeasible
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) (q : Fin T → ℝ) : Prop :=
  (∀ t, prob.Pmin ≤ q t ∧ q t ≤ prob.Pmax) ∧
    (∀ t : Fin (T - 1),
      |q (nextPeriod prob.hT t) - q (Fin.castLEOrderEmb (Nat.sub_le T 1) t)| ≤ prob.R)

def SingleGeneratorDispatchProblem.phiDef
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) (u : ℝ) : ℝ :=
  prob.α * u + prob.β * u^2

def SingleGeneratorDispatchProblem.psiDef
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) (v : ℝ) : ℝ :=
  prob.γ * |v|

theorem exists_prices_as_lagrange_multipliers_for_single_generator_subproblems
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
    (pStar : Fin n → Fin T → ℝ)
    (Q : Fin T → ℝ)
    (hgen :
      ∀ i : Fin n,
        SingleGeneratorDispatchProblem.IsFeasible
            { Q := Q
              Pmin := prob.Pmin i
              Pmax := prob.Pmax i
              R := prob.R i
              α := prob.α i
              β := prob.β i
              γ := prob.γ i
              hT := prob.hT
              alpha_pos := prob.alpha_pos i
              beta_pos := prob.beta_pos i
              gamma_pos := prob.gamma_pos i } (pStar i) ∧
        ∀ q : Fin T → ℝ,
          SingleGeneratorDispatchProblem.IsFeasible
            { Q := Q
              Pmin := prob.Pmin i
              Pmax := prob.Pmax i
              R := prob.R i
              α := prob.α i
              β := prob.β i
              γ := prob.γ i
              hT := prob.hT
              alpha_pos := prob.alpha_pos i
              beta_pos := prob.beta_pos i
              gamma_pos := prob.gamma_pos i } q →
          SingleGeneratorDispatchProblem.objective
              { Q := Q
                Pmin := prob.Pmin i
                Pmax := prob.Pmax i
                R := prob.R i
                α := prob.α i
                β := prob.β i
                γ := prob.γ i
                hT := prob.hT
                alpha_pos := prob.alpha_pos i
                beta_pos := prob.beta_pos i
                gamma_pos := prob.gamma_pos i } (pStar i) ≤
            SingleGeneratorDispatchProblem.objective
              { Q := Q
                Pmin := prob.Pmin i
                Pmax := prob.Pmax i
                R := prob.R i
                α := prob.α i
                β := prob.β i
                γ := prob.γ i
                hT := prob.hT
                alpha_pos := prob.alpha_pos i
                beta_pos := prob.beta_pos i
                gamma_pos := prob.gamma_pos i } q) :
      ∀ q : Fin n → Fin T → ℝ,
        MultiPeriodEconomicDispatch.IsFeasible prob q →
        @lagrangian
          (Fin n → Fin T → ℝ)
          (Fin T)
          (Fin 0)
          inferInstance
          inferInstance
          (fun q : Fin n → Fin T → ℝ => prob.objective q)
          (fun t q => ∑ i, q i t - prob.d t)
          (fun _ _ => 0)
          pStar
          Q
          (fun k => 0) ≤
        @lagrangian
          (Fin n → Fin T → ℝ)
          (Fin T)
          (Fin 0)
          inferInstance
          inferInstance
          (fun q : Fin n → Fin T → ℝ => prob.objective q)
          (fun t q => ∑ i, q i t - prob.d t)
          (fun _ _ => 0)
          q
          Q
          (fun k => 0) := by
  sorry

end «CAM-Bench-208»
