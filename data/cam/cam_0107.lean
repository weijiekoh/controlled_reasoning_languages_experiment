import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-107»

theorem blockDiagonal_has_eigenvalue_from_block
    {𝕜 : Type _} [RCLike 𝕜]
    {m : ℕ}
    {n : Fin m → Type _}
    [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)]
    (hsize : ∀ i : Fin m, Fintype.card (n i) = 1 ∨ Fintype.card (n i) = 2)
    (B : ∀ i, Matrix (n i) (n i) 𝕜) :
    (∀ μ : 𝕜,
      (∃ w, Module.End.HasEigenvector (Matrix.toLin' (Matrix.blockDiagonal' B)) μ w) ↔
        ∃ i : Fin m, ∃ v : n i → 𝕜, Module.End.HasEigenvector (Matrix.toLin' (B i)) μ v) ∧
    ∀ (i : Fin m) (μ : 𝕜) (v : n i → 𝕜),
      Module.End.HasEigenvector (Matrix.toLin' (B i)) μ v →
        Module.End.HasEigenvector
          (Matrix.toLin' (Matrix.blockDiagonal' B))
          μ
          (fun j =>
            if h : j.1 = i then
              v (cast (by cases h; rfl) j.2)
            else 0) := by
  sorry

end «CAM-Bench-107»
