import Mathlib

namespace Problem22

/--
Let $F$ be a field with $\mathbb{Q} \subseteq F \subseteq \mathbb{C}$, where $F/\mathbb{Q}$
is a finite \emph{abelian} Galois extension. Prove that $F$ contains only finitely many algebraic
integers (i.e. elements in $F$ whose minimal polynomial over $\mathbb{Q}$ have coefficients in
$\mathbb{Z}$) having absolute value $1$, and each of the algebraic integers is a root of unity.
-/
theorem finite_algebraic_integers_of_finite_module
    (F : IntermediateField ℚ ℂ) (h_fin : Module.Finite ℚ F) [IsGalois ℚ F]
    (h : IsMulCommutative (F ≃ₐ[ℚ] F)) : {x : F | IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1}.Finite ∧
    (∀ x : F, IsIntegral ℤ x → ‖(x : ℂ)‖ = 1 → ∃ n,  x ^ n = 1) := by
  have : NumberField F := ⟨⟩
  have hN : Normal ℚ F := inferInstance
  have L : ∀ ψ : F →ₐ[ℚ] ℂ, ∃ σ : F ≃ₐ[ℚ] F, ∀ a, ((σ a : F) : ℂ) = ψ a := by
    intro ψ
    have hm : ∀ a, ψ a ∈ F := by
      intro a
      have := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ F hN ψ
      exact (SetLike.ext_iff.mp this (ψ a)).mp ⟨a, rfl⟩
    let σ : F →ₐ[ℚ] F := ψ.codRestrict F.toSubalgebra hm
    exact ⟨AlgEquiv.ofBijective σ (AlgHom.normal_bijective ℚ F F σ), fun a => rfl⟩
  obtain ⟨c, hc⟩ := L ((starRingEnd ℂ).toRatAlgHom.comp F.val)
  have hc' : ∀ a, ((c a : F) : ℂ) = (starRingEnd ℂ) (a : ℂ) := fun a => hc a
  have key : ∀ x : F, ‖(x : ℂ)‖ = 1 → ∀ φ : F →+* ℂ, ‖φ x‖ = 1 := by
    intro x hx φ
    obtain ⟨σ, hσ⟩ := L φ.toRatAlgHom
    have e : φ x = ((σ x : F) : ℂ) := (hσ x).symm
    have h1 : x * c x = 1 := by
      apply Subtype.ext
      have : ((x * c x : F) : ℂ) = (x:ℂ) * (starRingEnd ℂ) x := by
        simp [hc']
      rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq, hx]; simp
    have h2 : (σ x : ℂ) * (starRingEnd ℂ) (σ x : ℂ) = 1 := by
      have hcom : c (σ x) = σ (c x) := by
        have := h.is_comm.comm c σ
        exact (congrArg (fun f : F ≃ₐ[ℚ] F => f x) this)
      have : (starRingEnd ℂ) (σ x : ℂ) = ((c (σ x) : F) : ℂ) := by simp [hc']
      rw [this, hcom]
      have : ((σ x * σ (c x) : F) : ℂ) = 1 := by rw [← map_mul, h1]; simp
      simpa using this
    rw [e]
    have := Complex.mul_conj (σ x : ℂ)
    rw [h2, Complex.normSq_eq_norm_sq] at this
    have h3 : ((‖(σ x : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 := this.symm
    have h4 : ‖(σ x : ℂ)‖ ^ 2 = 1 := by exact_mod_cast h3
    nlinarith [norm_nonneg (σ x : ℂ)]
  refine ⟨?_, ?_⟩
  · refine (NumberField.Embeddings.finite_of_norm_le F ℂ 1).subset ?_
    intro x hx
    exact ⟨hx.1, fun φ => (key x hx.2 φ).le⟩
  · intro x hi hx
    obtain ⟨n, _, hn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one F ℂ hi (key x hx)
    exact ⟨n, hn⟩

end Problem22
