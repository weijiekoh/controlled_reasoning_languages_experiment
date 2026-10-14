import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-576»

def IsProperConvexCone {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  Convex ℝ K ∧
  (∀ ⦃x y⦄, x ∈ K → y ∈ K → x + y ∈ K) ∧
  (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K) ∧
  K.Nonempty ∧
  IsClosed K ∧
  K ∩ (-K) = ({0} : Set (EuclideanSpace ℝ (Fin m))) ∧
  (interior K).Nonempty

def GeneralizedInequality {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → Prop :=
  fun y z => z - y ∈ K

def IsKConvex {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ ⦃x y : EuclideanSpace ℝ (Fin n)⦄ ⦃θ : ℝ⦄,
    θ ∈ Set.Icc (0 : ℝ) 1 →
    GeneralizedInequality K (f (θ • x + (1 - θ) • y)) (θ • f x + (1 - θ) • f y)

theorem kConvex_sublevel_set_convex {n m : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hK : IsProperConvexCone K)
    (hf : IsKConvex K f) :
    ∀ α : EuclideanSpace ℝ (Fin m),
      Convex ℝ {x : EuclideanSpace ℝ (Fin n) | GeneralizedInequality K (f x) α} := by
  intro α x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have h := hf (x := x) (y := y) (θ := a) ⟨ha, by linarith⟩
  simp only [Set.mem_setOf_eq, GeneralizedInequality] at *
  have key : α - f (a • x + (1 - a) • y) =
      a • (α - f x) + (1 - a) • (α - f y) +
        ((a • f x + (1 - a) • f y) - f (a • x + (1 - a) • y)) := by
    module
  rw [key]
  exact hK.2.1 (hK.2.1 (hK.2.2.1 ha hx) (hK.2.2.1 (by linarith) hy)) h

end «CAM-Bench-576»
