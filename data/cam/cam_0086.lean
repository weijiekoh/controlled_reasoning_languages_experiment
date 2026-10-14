import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-86»

def KKTConditions
    {n mℓ mi : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mℓ))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mi))
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h' : EuclideanSpace ℝ (Fin n) → (Fin mℓ → EuclideanSpace ℝ (Fin n)))
    (g' : EuclideanSpace ℝ (Fin n) → (Fin mi → EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ v, (fderiv ℝ f x) v = ⟪f' x, v⟫) ∧
    ∃ (lam : EuclideanSpace ℝ (Fin mℓ)) (mu : EuclideanSpace ℝ (Fin mi)),
      f' x
        - ∑ i : Fin mℓ, (lam i) • h' x i
        - ∑ i : Fin mi, (mu i) • g' x i
        = 0
        ∧ h x = 0
        ∧ ∀ i : Fin mi, 0 ≤ g x i
        ∧ ∀ i : Fin mi, 0 ≤ mu i
        ∧ ∀ i : Fin mi, mu i * g x i = 0

def SlackVariableReformulation
    {n m : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ s : EuclideanSpace ℝ (Fin m), g x - s = 0 ∧ ∀ i : Fin m, 0 ≤ s i

def KKTMultiplier
    {n mℓ mi : ℕ}
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h' : EuclideanSpace ℝ (Fin n) → (Fin mℓ → EuclideanSpace ℝ (Fin n)))
    (g' : EuclideanSpace ℝ (Fin n) → (Fin mi → EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (lam : EuclideanSpace ℝ (Fin mℓ))
    (mu : EuclideanSpace ℝ (Fin mi)) : Prop :=
  f' x
    - ∑ i : Fin mℓ, (lam i) • h' x i
    - ∑ i : Fin mi, (mu i) • g' x i
    = 0

def KKTStationarity
    {n mE mI : ℕ}
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (AE : EuclideanSpace ℝ (Fin n) → (Fin mE → EuclideanSpace ℝ (Fin n)))
    (AI : EuclideanSpace ℝ (Fin n) → (Fin mI → EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin mE))
    (z : EuclideanSpace ℝ (Fin mI)) : Prop :=
  f' x
    - ∑ i : Fin mE, (y i) • AE x i
    - ∑ i : Fin mI, (z i) • AI x i
    = 0

def ComplementarySlackness
    {mI : ℕ}
    (s z : EuclideanSpace ℝ (Fin mI)) : Prop :=
  (∀ i : Fin mI, 0 ≤ s i) ∧
    (∀ i : Fin mI, 0 ≤ z i) ∧
    (∀ i : Fin mI, s i * z i = 0) ∧
    (fun i => s i * z i) = 0

def PrimalFeasibility
    {n mE mI : ℕ}
    (cE : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mE))
    (cI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mI))
    (x : EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin mI)) : Prop :=
  cE x = 0 ∧ cI x - s = 0 ∧ ∀ i : Fin mI, 0 ≤ s i

def DualFeasibility
    {mI : ℕ}
    (z : EuclideanSpace ℝ (Fin mI)) : Prop :=
  ∀ i : Fin mI, 0 ≤ z i

structure SlackVariableNonlinearProgram where
  n : ℕ
  mE : ℕ
  mI : ℕ
  f : EuclideanSpace ℝ (Fin n) → ℝ
  cE : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mE)
  cI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mI)

def SlackVariableNonlinearProgram.isFeasible
    (P : SlackVariableNonlinearProgram)
    (x : EuclideanSpace ℝ (Fin P.n))
    (s : EuclideanSpace ℝ (Fin P.mI)) : Prop :=
  P.cE x = 0 ∧ P.cI x - s = 0 ∧ ∀ i : Fin P.mI, 0 ≤ s i

def SlackVariableNonlinearProgram.originalFeasible
    (P : SlackVariableNonlinearProgram)
    (x : EuclideanSpace ℝ (Fin P.n)) : Prop :=
  P.cE x = 0 ∧ ∀ i : Fin P.mI, 0 ≤ P.cI x i

theorem slack_variable_kkt_iff_original_kkt
    {n mE mI : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (cE : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mE))
    (cI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mI))
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (AE : EuclideanSpace ℝ (Fin n) → (Fin mE → EuclideanSpace ℝ (Fin n)))
    (AI : EuclideanSpace ℝ (Fin n) → (Fin mI → EuclideanSpace ℝ (Fin n)))
    (hf' : ∀ x v, (fderiv ℝ f x) v = ⟪f' x, v⟫)
    (hAE :
      ∀ x i v, (fderiv ℝ (fun x => cE x i) x) v = ⟪AE x i, v⟫)
    (hAI :
      ∀ x i v, (fderiv ℝ (fun x => cI x i) x) v = ⟪AI x i, v⟫)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∃ s : EuclideanSpace ℝ (Fin mI),
      ∃ y : EuclideanSpace ℝ (Fin mE),
        ∃ z : EuclideanSpace ℝ (Fin mI),
          KKTStationarity f' AE AI x y z ∧
          PrimalFeasibility cE cI x s ∧
          DualFeasibility z ∧
          (fun i : Fin mI => s i * z i) = 0) ↔
      KKTConditions f cE cI f' AE AI x := by
  sorry

end «CAM-Bench-86»
