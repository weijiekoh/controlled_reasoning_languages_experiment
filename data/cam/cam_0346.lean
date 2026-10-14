import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-346»

structure RestrictedLogLikelihood (Θ : Type) where
  dom : Set Θ
  toFun : Θ → ℝ

instance {Θ : Type} : CoeFun (RestrictedLogLikelihood Θ) (fun _ => Θ → ℝ) where
  coe f := f.toFun

def logLikelihood {Θ X : Type} [MeasurableSpace X] (p : Θ → X → ENNReal) (x : X) :
    RestrictedLogLikelihood Θ :=
  { dom := {θ | 0 < p θ x}
    toFun := fun θ => if 0 < p θ x then Real.log ((p θ x).toReal) else 0 }

theorem logLikelihood_concave_exponentialFamily :
    ∀ {n : ℕ},
      (∀ {D : Type} [Fintype D] [MeasurableSpace D] (c : D → Fin n → ℝ) (x : D),
          let p : (Fin n → ℝ) → D → ENNReal :=
            fun (theta : Fin n → ℝ) (y : D) =>
              (∑ z : D, ENNReal.ofReal (Real.exp (∑ i : Fin n, theta i * c z i)))⁻¹ *
                ENNReal.ofReal (Real.exp (∑ i : Fin n, theta i * c y i))
          ConcaveOn ℝ (logLikelihood p x).dom (logLikelihood p x))
      ∧
      (∀ {m : ℕ} (s : Set (Fin m → ℝ)) (hs : MeasurableSet s)
          (c : (Fin m → ℝ) → Fin n → ℝ) (x : Fin m → ℝ),
          x ∈ s →
          let p : (Fin n → ℝ) → (Fin m → ℝ) → ENNReal :=
            fun (theta : Fin n → ℝ) (y : Fin m → ℝ) =>
              (∫⁻ z in s, ENNReal.ofReal (Real.exp (∑ i : Fin n, theta i * c z i)))⁻¹ *
                ENNReal.ofReal (Real.exp (∑ i : Fin n, theta i * c y i))
          ConcaveOn ℝ (logLikelihood p x).dom (logLikelihood p x)) := by
  sorry

end «CAM-Bench-346»
