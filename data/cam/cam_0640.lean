import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-640»

def optimalValueFunction (f : α → ε → ℝ) (X : Set α) : ε → ℝ :=
  fun e => sInf ((fun x => f x e) '' X)

def IsAffineOnInterval (g : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ a c : ℝ, ∀ ε ∈ I, g ε = a * ε + c

open scoped BigOperators

structure ParametricL1ResidualMinimization where
  A : Matrix (Fin 6) (Fin 3) ℝ
  b : Fin 6 → ℝ
  d : Fin 6 → ℝ

def ParametricL1ResidualMinimization.objective
    (P : ParametricL1ResidualMinimization) (ε : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 6, |(∑ j : Fin 3, P.A i j * x j) + P.b i + ε * P.d i|

def ParametricL1ResidualMinimization.feasibleSet : Set (Fin 3 → ℝ) :=
  Set.univ

def ParametricL1ResidualMinimization.optimalValue
    (P : ParametricL1ResidualMinimization) : ℝ → ℝ :=
  optimalValueFunction (fun x ε => P.objective ε x) ParametricL1ResidualMinimization.feasibleSet

def ParametricL1ResidualMinimization.pStar
    (P : ParametricL1ResidualMinimization) : ℝ → ℝ :=
  optimalValueFunction (fun x ε => P.objective ε x) ParametricL1ResidualMinimization.feasibleSet

theorem optimalValue_affineOnInterval_containing_zero :
    ∃ I : Set ℝ,
      Set.OrdConnected I ∧
      0 ∈ I ∧
      IsAffineOnInterval
        ({ A := ![![(-2 : ℝ), 7, 1],
                 ![-5, -1, 3],
                 ![-7, 3, -5],
                 ![-1, 4, -4],
                 ![1, 5, 5],
                 ![2, -5, -1]],
           b := ![-4, 3, 9, 0, -11, 5],
           d := ![-10, -13, -27, -10, -7, 14] } :
          ParametricL1ResidualMinimization).optimalValue I := by
  sorry

end «CAM-Bench-640»
