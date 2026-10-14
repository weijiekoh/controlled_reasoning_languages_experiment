import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-374»

def newtonStep
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (fHess : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (fGrad : (Fin n → ℝ) → Fin n → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (xHat : Fin n → ℝ)
    (dx : Fin n → ℝ := fun _ => 0) : Prop :=
  let _ := f xHat
  ∃ b : Fin m → ℝ,
    A.mulVec xHat = b ∧
      ∃ nu : Fin m → ℝ,
        (fHess xHat).mulVec dx + A.transpose.mulVec nu = -(fGrad xHat) ∧
          A.mulVec dx = 0

def newtonDecrement
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (fHess : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (fGrad : (Fin n → ℝ) → Fin n → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (xHat : Fin n → ℝ)
    (hstep : ∃ dx : Fin n → ℝ, newtonStep f fHess fGrad A xHat dx) : ℝ :=
  let dx : Fin n → ℝ := Classical.choose hstep
  Real.sqrt (-∑ i, fGrad xHat i * dx i)

structure QuadraticConstrainedLinearProgram where
  n : ℕ
  m : ℕ
  fGrad : (Fin n → ℝ) → Fin n → ℝ
  fHess : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  xHat : Fin n → ℝ

def QuadraticConstrainedLinearProgram.objectiveFn
    (p : QuadraticConstrainedLinearProgram) (y : Fin p.n → ℝ) : ℝ :=
  ∑ i, p.fGrad p.xHat i * y i

def QuadraticConstrainedLinearProgram.feasibleSet
    (p : QuadraticConstrainedLinearProgram) (y : Fin p.n → ℝ) : Prop :=
  p.A.mulVec y = 0 ∧
    (∑ i, y i * ∑ j, p.fHess p.xHat i j * y j) ≤ 1

theorem quadratic_constrained_linear_program_unique_solution
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (fHess : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (fGrad : (Fin n → ℝ) → Fin n → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (xHat Δx : Fin n → ℝ)
    (hconvex : Convex ℝ (Set.univ : Set (Fin n → ℝ)))
    (hC2 : ContDiff ℝ 2 f)
    (hArank : Module.rank ℝ (Fin m → ℝ) = m)
    (hxb : A.mulVec xHat = b)
    (hstep : newtonStep f fHess fGrad A xHat Δx)
    (hKKT :
      ∃! z : (Fin n → ℝ) × (Fin m → ℝ),
        (fHess xHat).mulVec z.1 + A.transpose.mulVec z.2 = -(fGrad xHat) ∧
          A.mulVec z.1 = 0)
    (hdec : ℝ := newtonDecrement f fHess fGrad A xHat ⟨Δx, hstep⟩)
    (hdec_eq : hdec = Real.sqrt (-∑ i, fGrad xHat i * Δx i))
    (hKKT_nonsingular : ∃! z : (Fin n → ℝ) × (Fin m → ℝ),
      (fHess xHat).mulVec z.1 + A.transpose.mulVec z.2 = -(fGrad xHat) ∧
        A.mulVec z.1 = 0)
    (hlam_pos : 0 < hdec) :
    ∃! y : Fin n → ℝ,
      A.mulVec y = 0 ∧
        (∑ i, y i * ∑ j, fHess xHat i j * y j) ≤ 1 ∧
        (∀ z : Fin n → ℝ,
          A.mulVec z = 0 ∧
            (∑ i, z i * ∑ j, fHess xHat i j * z j) ≤ 1 →
          (∑ i, fGrad xHat i * y i) ≤ ∑ i, fGrad xHat i * z i) ∧
        y = fun i => Δx i / hdec :=
by
  sorry

end «CAM-Bench-374»
