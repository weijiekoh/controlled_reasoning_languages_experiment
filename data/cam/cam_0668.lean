import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-668»

def QuasiconvexOn {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (C : Set E) (f : E → WithTop ℝ) : Prop :=
  Convex ℝ C ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ θ : ℝ, ∀ hθ : θ ∈ Set.Icc (0 : ℝ) 1,
      f (θ • x + (1 - θ) • y) ≤ f x ∧
        f (θ • x + (1 - θ) • y) ≤ f y

structure RationalChebyshevFittingProblem where
  m : ℕ
  n : ℕ
  k : ℕ
  α : ℝ
  β : ℝ
  hαβ : α ≤ β
  t : Fin k → ℝ
  y : Fin k → ℝ
  ht_mem : ∀ i : Fin k, t i ∈ Set.Icc α β

def RationalChebyshevFittingProblem.p
    (P : RationalChebyshevFittingProblem) :
    (Fin (P.m + 1) → ℝ) → ℝ → ℝ :=
  fun a t => ∑ j : Fin (P.m + 1), a j * t ^ (j : ℕ)

def RationalChebyshevFittingProblem.q
    (P : RationalChebyshevFittingProblem) :
    (Fin P.n → ℝ) → ℝ → ℝ :=
  fun b t => 1 + ∑ j : Fin P.n, b j * t ^ ((j : ℕ) + 1)

def RationalChebyshevFittingProblem.domain
    (P : RationalChebyshevFittingProblem) :
    Set ((Fin (P.m + 1) → ℝ) × (Fin P.n → ℝ)) :=
  {ab | ∀ t : ℝ, t ∈ Set.Icc P.α P.β → 0 < P.q ab.2 t}

def RationalChebyshevFittingProblem.objective
    (P : RationalChebyshevFittingProblem) :
    ((Fin (P.m + 1) → ℝ) × (Fin P.n → ℝ)) → ℝ :=
  fun ab =>
    sSup (Set.range fun i : Fin P.k =>
      (|P.p ab.1 (P.t i) / P.q ab.2 (P.t i) - P.y i| : ℝ))

theorem rationalChebyshevFittingProblem_quasiconvex
    (P : RationalChebyshevFittingProblem) :
    QuasiconvexOn P.domain (fun ab => (P.objective ab : WithTop ℝ)) := by
  sorry

end «CAM-Bench-668»
