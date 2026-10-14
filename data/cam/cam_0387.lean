import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-387»

structure ConvexQuadraticProgram (n m p : ℕ) where
  Q : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  r : ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  G : Matrix (Fin p) (Fin n) ℝ
  h : Fin p → ℝ
  convex : Q.PosSemidef

def ConvexQuadraticProgram.objective {n m p : ℕ} (P : ConvexQuadraticProgram n m p)
    (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.Q.mulVec x) + dotProduct P.c x + P.r

def ConvexQuadraticProgram.satisfiesEqConstraints {n m p : ℕ} (P : ConvexQuadraticProgram n m p)
    (x : Fin n → ℝ) : Prop :=
  P.A.mulVec x = P.b

def ConvexQuadraticProgram.satisfiesIneqConstraints {n m p : ℕ} (P : ConvexQuadraticProgram n m p)
    (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin p, (P.G.mulVec x) i ≤ P.h i

def ConvexQuadraticProgram.isFeasible {n m p : ℕ} (P : ConvexQuadraticProgram n m p)
    (x : Fin n → ℝ) : Prop :=
  P.satisfiesEqConstraints x ∧ P.satisfiesIneqConstraints x

structure SignConstrainedLeastSquaresProblem (n : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  S : Matrix (Fin n) (Fin n) ℝ
  s : Fin n → ℝ

def SignConstrainedLeastSquaresProblem.residual {n : ℕ}
    (P : SignConstrainedLeastSquaresProblem n) (a b : Fin n → ℝ) : Fin n → ℝ :=
  P.C.mulVec a + P.S.mulVec b

def SignConstrainedLeastSquaresProblem.satisfiesSignConstraints {n : ℕ}
    (P : SignConstrainedLeastSquaresProblem n) (a b : Fin n → ℝ) : Prop :=
  ∀ t : Fin n, P.s t * (P.residual a b) t ≥ 0

def SignConstrainedLeastSquaresProblem.satisfiesNormalization {n : ℕ}
    (P : SignConstrainedLeastSquaresProblem n) (a b : Fin n → ℝ) : Prop :=
  ∑ t : Fin n, P.s t * (P.residual a b) t = n

def SignConstrainedLeastSquaresProblem.standard {n : ℕ}
    (C S : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) :
    SignConstrainedLeastSquaresProblem n where
  C := C
  S := S
  s := s

def SignConstrainedLeastSquaresProblem.objective {n : ℕ}
    (P : SignConstrainedLeastSquaresProblem n) (a b : Fin n → ℝ) : ℝ :=
  ‖P.residual a b‖ ^ 2

def SignConstrainedLeastSquaresProblem.objectiveFn {n : ℕ}
    (P : SignConstrainedLeastSquaresProblem n) (a b : Fin n → ℝ) : ℝ :=
  P.objective a b

def SignConstrainedLeastSquaresProblem.isFeasible {n : ℕ}
    (P : SignConstrainedLeastSquaresProblem n) (a b : Fin n → ℝ) : Prop :=
  P.satisfiesSignConstraints a b ∧ P.satisfiesNormalization a b

theorem sign_normalized_least_squares_is_convex_quadratic_program
    (n B : ℕ) (hB : B ≥ 1) (f_min : ℤ) (s : Fin n → ℝ)
    (hsign : ∀ t : Fin n, s t = 1 ∨ s t = -1)
    (hstrict :
      ∃ a : Fin B → ℝ, ∃ b : Fin B → ℝ,
        ∀ t : Fin n,
          s t *
            ((∑ j : Fin B,
                a j *
                  Real.cos
                    (((2 * Real.pi) / (n : ℝ)) *
                      (((f_min : ℝ) + (((j : ℕ) + 1 : ℝ) - 1)) * (((t : ℕ) + 1 : ℝ))))) +
              (∑ j : Fin B,
                b j *
                  Real.sin
                    (((2 * Real.pi) / (n : ℝ)) *
                      (((f_min : ℝ) + (((j : ℕ) + 1 : ℝ) - 1)) * (((t : ℕ) + 1 : ℝ)))))) > 0) :
    ∃ C : Matrix (Fin n) (Fin B) ℝ,
      ∃ S : Matrix (Fin n) (Fin B) ℝ,
        (∀ t : Fin n, ∀ j : Fin B,
          C t j =
            Real.cos
              (((2 * Real.pi) / (n : ℝ)) *
                (((f_min : ℝ) + (((j : ℕ) + 1 : ℝ) - 1)) * (((t : ℕ) + 1 : ℝ))))) ∧
        (∀ t : Fin n, ∀ j : Fin B,
          S t j =
            Real.sin
              (((2 * Real.pi) / (n : ℝ)) *
                (((f_min : ℝ) + (((j : ℕ) + 1 : ℝ) - 1)) * (((t : ℕ) + 1 : ℝ))))) ∧
        ∃ P : SignConstrainedLeastSquaresProblem n,
          P.s = s ∧
          (∀ a b : Fin B → ℝ,
            P.objective
              (fun i => if h : i.1 < B then a ⟨i.1, h⟩ else 0)
              (fun i => if h : i.1 < B then b ⟨i.1, h⟩ else 0) =
            ‖C.mulVec a + S.mulVec b‖ ^ 2) ∧
          (∀ a b : Fin B → ℝ,
            P.isFeasible
              (fun i => if h : i.1 < B then a ⟨i.1, h⟩ else 0)
              (fun i => if h : i.1 < B then b ⟨i.1, h⟩ else 0) ↔
              (∀ t : Fin n, s t * (C.mulVec a + S.mulVec b) t ≥ 0) ∧
              (∑ t : Fin n, s t * (C.mulVec a + S.mulVec b) t = n)) := by
  sorry

end «CAM-Bench-387»
