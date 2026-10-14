import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-334»

def PiecewiseAffine (f : ℝ → ℝ) : Prop :=
  ∃ (n : ℕ) (s : Fin (n + 1) → Set ℝ) (a b : Fin (n + 1) → ℝ),
    (∀ i, ∃ l u : ℝ, s i = Set.Icc l u ∨ s i = Set.Ioo l u ∨ s i = Set.Ioc l u ∨ s i = Set.Ico l u) ∧
    (∀ i, ∀ t ∈ s i, f t = a i * t + b i) ∧
    (⋃ i, s i) = Set.univ ∧
    (∀ i j, i ≠ j → Disjoint (s i) (s j))

def KnotPoints (f : ℝ → ℝ) (p : Finset ℝ) : Prop :=
  ∀ {x y : ℝ}, x ≤ y →
    (∀ t, x < t → t < y → t ∉ p) →
    ∃ a b : ℝ, ∀ t, x ≤ t → t ≤ y → f t = a * t + b

structure ConvexSplineRegressionProblem where
  N : ℕ
  n : ℕ
  K : ℕ
  x : Fin N → Fin n → ℝ
  y : Fin N → ℝ
  p : Fin K → ℝ
  lam : ℝ
  alpha : ℝ
  a : Fin n → ℝ
  b : Fin n → ℝ
  u : Fin n → Fin K → ℝ

def ConvexSplineRegressionProblem.posPart (t : ℝ) : ℝ :=
  max t 0

def ConvexSplineRegressionProblem.predict (P : ConvexSplineRegressionProblem) (i : Fin P.N) : ℝ :=
  P.alpha + ∑ j : Fin P.n, (P.a j + P.b j * P.x i j + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (P.x i j - P.p k))

def ConvexSplineRegressionProblem.residual (P : ConvexSplineRegressionProblem) (i : Fin P.N) : ℝ :=
  P.y i - P.predict i

def ConvexSplineRegressionProblem.objective (P : ConvexSplineRegressionProblem) : ℝ :=
  (1 / (P.N : ℝ)) * ∑ i : Fin P.N, (P.residual i) ^ 2
    + P.lam * ∑ j : Fin P.n, ∑ k : Fin P.K, |P.u j k|

def ConvexSplineRegressionProblem.satisfiesNormalization (P : ConvexSplineRegressionProblem) : Prop :=
  ∀ j : Fin P.n,
    P.a j + P.b j * 0 + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (0 - P.p k) = 0

def ConvexSplineRegressionProblem.isFeasible (P : ConvexSplineRegressionProblem) : Prop :=
  P.satisfiesNormalization

theorem piecewiseAffineRegression_equivalent_to_convexSplineRegression
    (P : ConvexSplineRegressionProblem)
    (hN : 1 ≤ P.N)
    (hn : 1 ≤ P.n)
    (hK : 1 ≤ P.K)
    (hlam : 0 < P.lam)
    (hp_strictMono : StrictMono P.p)
    (hfeas : P.isFeasible) :
    (∀ j : Fin P.n,
      Continuous
        (fun t =>
          P.a j + P.b j * t
            + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (t - P.p k))) ∧
    (∀ j : Fin P.n,
      PiecewiseAffine
        (fun t =>
          P.a j + P.b j * t
            + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (t - P.p k))) ∧
    (∀ j : Fin P.n,
      KnotPoints
        (fun t =>
          P.a j + P.b j * t
            + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (t - P.p k))
        (Finset.univ.image P.p)) ∧

    ConvexOn ℝ Set.univ
      (fun params : ℝ × (Fin P.n → ℝ) × (Fin P.n → ℝ) × (Fin P.n → Fin P.K → ℝ) =>
        (1 / (P.N : ℝ)) *
          ∑ i : Fin P.N,
            (P.y i - params.1 -
              ∑ j : Fin P.n,
                (params.2.1 j + params.2.2.1 j * P.x i j +
                  ∑ k : Fin P.K,
                    params.2.2.2 j k *
                      ConvexSplineRegressionProblem.posPart (P.x i j - P.p k))) ^ 2 +
        P.lam * ∑ j : Fin P.n, ∑ k : Fin P.K, |params.2.2.2 j k|) := by
  sorry

end «CAM-Bench-334»
