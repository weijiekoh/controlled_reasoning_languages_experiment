import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-284»

def IsConvexOptimizationProblem
    {E ι : Type*}
    [AddCommMonoid E]
    [Module ℝ E]
    (s : Set E)
    (f : E → ℝ)
    (g : ι → E → ℝ) : Prop :=
  Convex ℝ s ∧ ConvexOn ℝ s f ∧ ∀ i : ι, ConvexOn ℝ s (g i)

def perspective {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) × {t : ℝ // 0 < t} → EReal :=
  fun xt => (xt.2 : ℝ) * f (fun i => xt.1 i / (xt.2 : ℝ))

structure FuelOptimalTravelTimeProgram where
  n : ℕ
  d : Fin n → ℝ
  Phi : ℝ → EReal
  sMax : ℝ
  sMin : ℝ
  tauMin : Fin n → ℝ
  tauMax : Fin n → ℝ

def FuelOptimalTravelTimeProgram.objective
    (P : FuelOptimalTravelTimeProgram) (t : Fin P.n → ℝ) : EReal :=
  ∑ i, (t i : EReal) * P.Phi (P.d i / t i)

def FuelOptimalTravelTimeProgram.feasible
    (P : FuelOptimalTravelTimeProgram) (t : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.n, P.d i / P.sMax ≤ t i ∧ t i ≤ P.d i / P.sMin) ∧
    ∀ i : Fin P.n,
      P.tauMin i ≤ ∑ j : Fin (i.1 + 1), t ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ ∧
        ∑ j : Fin (i.1 + 1), t ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ ≤ P.tauMax i

def FuelOptimalTravelTimeProgram.optimalSpeed
    (P : FuelOptimalTravelTimeProgram) (t : Fin P.n → ℝ) (i : Fin P.n) : ℝ :=
  P.d i / t i

theorem speed_formulation_equivalent_to_fuel_optimal_travel_time_program
    (P : FuelOptimalTravelTimeProgram)
    (hPhi_pos : ∀ x : ℝ, 0 ≤ P.Phi x)
    (hPhi_mono : Monotone P.Phi)
    (hPhi_convex : ConvexOn ℝ Set.univ (fun x => (P.Phi x).toReal))
    (hn : 1 ≤ P.n)
    (hd : ∀ i : Fin P.n, 0 < P.d i)
    (hs : 0 < P.sMin ∧ P.sMin ≤ P.sMax) :
    (∃ s : Fin P.n → ℝ,
      (∀ i : Fin P.n, P.sMin ≤ s i ∧ s i ≤ P.sMax) ∧
      (∀ i : Fin P.n,
        P.tauMin i ≤ ∑ j : Fin (i.1 + 1),
          P.d ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ /
            s ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ ∧
        ∑ j : Fin (i.1 + 1),
          P.d ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ /
            s ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ ≤ P.tauMax i) ∧
      ∀ s' : Fin P.n → ℝ,
        ((∀ i : Fin P.n, P.sMin ≤ s' i ∧ s' i ≤ P.sMax) ∧
          (∀ i : Fin P.n,
            P.tauMin i ≤ ∑ j : Fin (i.1 + 1),
              P.d ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ /
                s' ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ ∧
            ∑ j : Fin (i.1 + 1),
              P.d ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ /
                s' ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ ≤ P.tauMax i) →
          (∑ i : Fin P.n, ((P.d i / s i : ℝ) : EReal) * P.Phi (s i)) ≤
            ∑ i : Fin P.n, ((P.d i / s' i : ℝ) : EReal) * P.Phi (s' i)))
    ↔
    (∃ t : Fin P.n → ℝ,
      P.feasible t ∧
      ∀ t' : Fin P.n → ℝ, P.feasible t' → P.objective t ≤ P.objective t') := by
  sorry

end «CAM-Bench-284»
