import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-329»

open scoped RealInnerProductSpace

def convexConjugate {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → EReal) :
    EuclideanSpace ℝ (Fin m) → EReal :=
  fun y => sSup (Set.range fun v => ((⟪y, v⟫ : ℝ) : EReal) - h v)

structure ConvexInequalityConstrainedProblem (n m : ℕ) where
  domain : Set (EuclideanSpace ℝ (Fin n))
  domain_convex : Convex ℝ domain
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  constraints : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  objective_convex : ConvexOn ℝ domain objective
  constraints_convex : ∀ i : Fin m, ConvexOn ℝ domain (constraints i)

def ConvexInequalityConstrainedProblem.isFeasible
    {n m : ℕ} (P : ConvexInequalityConstrainedProblem n m)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ P.domain ∧ ∀ i : Fin m, P.constraints i x ≤ 0

def ConvexInequalityConstrainedProblem.objectiveValue
    {n m : ℕ} (P : ConvexInequalityConstrainedProblem n m)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.objective x

theorem perturbationValue_eq_convexConjugate_negDual_on_interiorDom
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar g : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    (hg : g =
      fun lam =>
        if ∀ i : Fin m, 0 ≤ lam i then
          sInf <|
            Set.range fun x : {x // x ∈ P.domain} =>
              (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal)
        else
          ⊥)
    {u : EuclideanSpace ℝ (Fin m)}
    (hu : u ∈ interior {v | pStar v < ⊤}) :
    pStar u = convexConjugate (fun y => -g y) (-u) := by
  sorry

end «CAM-Bench-329»
