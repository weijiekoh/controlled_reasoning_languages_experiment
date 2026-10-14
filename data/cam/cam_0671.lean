import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-671»

def IsMaximumLikelihoodEstimate {Θ Y : Type _} (p : Θ → Y → ℝ) (feasible : Set Θ) (y : Y)
    (θhat : Θ) : Prop :=
  θhat ∈ feasible ∧ ∀ θ, θ ∈ feasible → p θ y ≤ p θhat y

open scoped BigOperators

theorem mle_uniform_noise_iff_minimizes_infNorm_residual
    {m n : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (xalpha_hat : (Fin n → ℝ) × ℝ) :
    IsMaximumLikelihoodEstimate
        (fun xa : (Fin n → ℝ) × ℝ => fun y' : Fin m → ℝ =>
          if hfeas : 0 ≤ xa.2 ∧
              ∀ i : Fin m, |y' i - ∑ j : Fin n, A i j * xa.1 j| ≤ xa.2 then
            if hzero : xa.2 = 0 then
              if (sSup (Set.range fun i : Fin m => |y' i - ∑ j : Fin n, A i j * xa.1 j|)) = 0
              then 1 else 0
            else
              (1 / (2 * xa.2)) ^ m
          else 0)
        {xa : (Fin n → ℝ) × ℝ | 0 ≤ xa.2}
        y
        xalpha_hat
        ↔
        ((∀ x : Fin n → ℝ,
            sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * xalpha_hat.1 j - y i|) ≤
              sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * x j - y i|)) ∧
          xalpha_hat.2 =
            sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * xalpha_hat.1 j - y i|)) := by
  sorry

end «CAM-Bench-671»
