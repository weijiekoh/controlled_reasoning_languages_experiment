import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-392»

structure SecondOrderConeProgram where
  n : ℕ
  m : ℕ
  objective : Fin n → ℝ
  equalityRows : ℕ
  equalityMatrix : Fin equalityRows → Fin n → ℝ
  equalityRhs : Fin equalityRows → ℝ
  coneMatrix : Fin m → Type
  coneMap : (i : Fin m) → coneMatrix i → Fin n → ℝ
  coneOffset : (i : Fin m) → coneMatrix i → ℝ
  coneLinear : Fin m → Fin n → ℝ
  coneScalar : Fin m → ℝ

def SecondOrderConeProgram.objectiveValue (P : SecondOrderConeProgram) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.objective j * x j

def SecondOrderConeProgram.satisfiesEqualities (P : SecondOrderConeProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ r : Fin P.equalityRows,
    (∑ j : Fin P.n, P.equalityMatrix r j * x j) = P.equalityRhs r

def SecondOrderConeProgram.satisfiesConeConstraint (P : SecondOrderConeProgram) (i : Fin P.m)
    (x : Fin P.n → ℝ) : Prop :=
  ∃ _inst : Fintype (P.coneMatrix i),
    Real.sqrt
        (∑ k : P.coneMatrix i,
          (((∑ j : Fin P.n, P.coneMap i k j * x j) + P.coneOffset i k) ^ 2)) ≤
      (∑ j : Fin P.n, P.coneLinear i j * x j) + P.coneScalar i

def SecondOrderConeProgram.isFeasible (P : SecondOrderConeProgram) (x : Fin P.n → ℝ) : Prop :=
  P.satisfiesEqualities x ∧ ∀ i : Fin P.m, P.satisfiesConeConstraint i x

structure DiscretizedAntennaOptimization where
  ι : Type*
  targetIndex : ι
  sampleValue : ι → ℝ

def DiscretizedAntennaOptimization.objectiveValue
    (P : DiscretizedAntennaOptimization) : ℝ :=
  sSup (Set.range fun j : P.ι => |P.sampleValue j|)

def DiscretizedAntennaOptimization.isFeasible (P : DiscretizedAntennaOptimization) : Prop :=
  P.sampleValue P.targetIndex = 1

structure AntennaDesignSOCP where
  n : ℕ
  ι : Type*
  a : ι → Fin (2 * n) → ℝ
  b : ι → Fin (2 * n) → ℝ
  targetIndex : ι

def AntennaDesignSOCP.primalObjective (P : AntennaDesignSOCP) (t : ℝ) : ℝ := t

def AntennaDesignSOCP.targetEqualities (P : AntennaDesignSOCP) (u : Fin (2 * P.n) → ℝ) : Prop :=
  (∑ k : Fin (2 * P.n), P.a P.targetIndex k * u k = 1) ∧
    (∑ k : Fin (2 * P.n), P.b P.targetIndex k * u k = 0)

def AntennaDesignSOCP.coneConstraint (P : AntennaDesignSOCP) (j : P.ι)
    (u : Fin (2 * P.n) → ℝ) (t : ℝ) : Prop :=
  Real.sqrt
      ((∑ k : Fin (2 * P.n), P.a j k * u k) ^ 2 + (∑ k : Fin (2 * P.n), P.b j k * u k) ^ 2) ≤ t

def AntennaDesignSOCP.isFeasible (P : AntennaDesignSOCP) (u : Fin (2 * P.n) → ℝ) (t : ℝ) : Prop :=
  P.targetEqualities u ∧ ∀ j : P.ι, P.coneConstraint j u t

theorem discretizedAntennaOptimization_equivalent_to_antennaDesignSOCP :
    ∀ (n : ℕ) (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]
      (x y : Fin n → ℝ) (wre wim : Fin n → ℝ)
      (θtar Δ : ℝ) (θ : ι → ℝ)
      (hI : ∃ j : ι, |θ j - θtar| ≥ Δ),
      let gamma : Fin n → ℝ → ℝ := fun k ang => x k * Real.cos ang + y k * Real.sin ang
      let I : Set ι := {j | |θ j - θtar| ≥ Δ}
      let a : ι → Fin (2 * n) → ℝ := fun j k =>
        if hk : k.1 < n then
          Real.cos (gamma ⟨k.1, hk⟩ (θ j))
        else
          -Real.sin (gamma ⟨k.1 - n, by
            have hn : n ≤ k.1 := Nat.le_of_not_lt hk
            have hk2 : k.1 < 2 * n := k.2
            omega⟩ (θ j))
      let b : ι → Fin (2 * n) → ℝ := fun j k =>
        if hk : k.1 < n then
          Real.sin (gamma ⟨k.1, hk⟩ (θ j))
        else
          Real.cos (gamma ⟨k.1 - n, by
            have hn : n ≤ k.1 := Nat.le_of_not_lt hk
            have hk2 : k.1 < 2 * n := k.2
            omega⟩ (θ j))
      let a_tar : Fin (2 * n) → ℝ := fun k =>
        if hk : k.1 < n then
          Real.cos (gamma ⟨k.1, hk⟩ θtar)
        else
          -Real.sin (gamma ⟨k.1 - n, by
            have hn : n ≤ k.1 := Nat.le_of_not_lt hk
            have hk2 : k.1 < 2 * n := k.2
            omega⟩ θtar)
      let b_tar : Fin (2 * n) → ℝ := fun k =>
        if hk : k.1 < n then
          Real.sin (gamma ⟨k.1, hk⟩ θtar)
        else
          Real.cos (gamma ⟨k.1 - n, by
            have hn : n ≤ k.1 := Nat.le_of_not_lt hk
            have hk2 : k.1 < 2 * n := k.2
            omega⟩ θtar)
      let u : Fin (2 * n) → ℝ := fun k =>
        if hk : k.1 < n then
          wre ⟨k.1, hk⟩
        else
          wim ⟨k.1 - n, by
            have hn : n ≤ k.1 := Nat.le_of_not_lt hk
            have hk2 : k.1 < 2 * n := k.2
            omega⟩
      ((sSup (Set.range fun j : {j : ι // j ∈ I} =>
          Real.sqrt
            ((∑ k : Fin (2 * n), a j.1 k * u k) ^ 2 +
             (∑ k : Fin (2 * n), b j.1 k * u k) ^ 2)) =
        sInf {t : ℝ |
          (∑ k : Fin (2 * n), a_tar k * u k = 1) ∧
          (∑ k : Fin (2 * n), b_tar k * u k = 0) ∧
          ∀ j : {j : ι // j ∈ I},
            Real.sqrt
              ((∑ k : Fin (2 * n), a j.1 k * u k) ^ 2 +
               (∑ k : Fin (2 * n), b j.1 k * u k) ^ 2) ≤ t})) := by
  sorry

end «CAM-Bench-392»
