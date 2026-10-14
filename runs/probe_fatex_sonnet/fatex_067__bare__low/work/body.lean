  classical
  intro e
  rcases e with ⟨e⟩
  set A := MvPowerSeries (Fin n) k with hA
  have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let X0 : A := MvPowerSeries.X i0
  let c : ℕ → (A →ₗ[k] k) := fun i => MvPowerSeries.coeff (Finsupp.single i0 i)
  have cX : ∀ j b, c (j+1) (X0 * b) = c j b := by
    intro j b
    have := MvPowerSeries.coeff_add_monomial_mul (R := k) (Finsupp.single i0 1) (Finsupp.single i0 j) b 1
    rw [← Finsupp.single_add, MvPowerSeries.X_def] at *
    simp only [c, X0]
    rw [MvPowerSeries.X_def, add_comm j 1]
    simpa using this
  have cX0 : ∀ b, c 0 (X0 * b) = 0 := by
    intro b
    simpa [c] using MvPowerSeries.coeff_zero_X_mul b i0
  let Λ : (A →ₗ[k] k) → (A ⊗[k] A →ₗ[k] A) := fun φ =>
    (TensorProduct.rid k A).toLinearMap ∘ₗ (TensorProduct.map LinearMap.id φ)
  have Λt : ∀ φ a b, Λ φ (a ⊗ₜ b) = φ b • a := by
    intro φ a b; simp [Λ]
  have Λm : ∀ φ (t : A ⊗[k] A), Λ φ ((X0 ⊗ₜ[k] X0) * t) = X0 * Λ (φ ∘ₗ LinearMap.mulLeft k X0) t := by
    intro φ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Λt, Λt]
      simp [mul_smul_comm]
  have Λ1 : ∀ φ, Λ φ 1 = φ 1 • (1:A) := by
    intro φ; rw [Algebra.TensorProduct.one_def, Λt]
  have fin : ∀ t : A ⊗[k] A, ∃ F : Submodule k A, Module.Finite k F ∧ ∀ φ, Λ φ t ∈ F := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨⊥, inferInstance, by simp⟩
    | tmul a b => exact ⟨k ∙ a, inferInstance, fun φ => by rw [Λt]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)⟩
    | add x y hx hy =>
      obtain ⟨F, hF, h1⟩ := hx
      obtain ⟨G, hG, h2⟩ := hy
      exact ⟨F ⊔ G, inferInstance, fun φ => by rw [map_add]; exact Submodule.add_mem_sup (h1 φ) (h2 φ)⟩
  -- augmentation
  let aug : A →ₐ[k] k := (MvPowerSeries.constantCoeff : A →+* k).toAlgHom_placeholder
  sorry
