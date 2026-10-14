import Mathlib

namespace Problem67

open scoped TensorProduct

/--
Let $A$ be the ring $k[[x_1, \dots, x_n]]$, where $k$ is a field, $n \in \mathbb{N}$, $n \ne 0$.
Show that there is \textbf{no} isomorphism
\[
A \otimes_k A \cong k[[x_1, \dots, x_n, y_1, \dots, y_n]].
\]
-/
theorem isEmpty_mvPowerSeries_tensor_mvPowerSeries_algEquiv
    {k : Type} [Field k] (n : ℕ) (hn : n ≠ 0) :
    IsEmpty ((MvPowerSeries (Fin n) k) ⊗[k] (MvPowerSeries (Fin n) k) ≃ₐ[k]
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
  have key : ∀ v : A ⊗[k] A, v = 1 + (X0 ⊗ₜ[k] X0) * v → ∀ i, Λ (c i) v = X0 ^ i := by
    intro v hv i
    induction i with
    | zero =>
      have := congrArg (Λ (c 0)) hv
      rw [map_add, Λm, Λ1] at this
      have h0 : (c 0 ∘ₗ LinearMap.mulLeft k X0) = 0 := by
        ext b; simp [cX0]
      rw [h0] at this
      simp at this
      simpa [c, MvPowerSeries.coeff_one] using this
    | succ j ih =>
      have := congrArg (Λ (c (j+1))) hv
      rw [map_add, Λm, Λ1] at this
      have h0 : (c (j+1) ∘ₗ LinearMap.mulLeft k X0) = c j := by
        ext b; simp [cX]
      rw [h0, ih] at this
      have h1 : c (j+1) 1 = 0 := by simp [c, MvPowerSeries.coeff_one, Finsupp.single_eq_zero]
      rw [h1] at this
      simpa [pow_succ, mul_comm] using this
  have LI : LinearIndependent k (fun i : ℕ => X0 ^ i) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have := congrArg (c i) hg
    simp only [map_sum, map_smul, map_zero] at this
    have hc : ∀ j, c i (X0 ^ j) = if i = j then 1 else 0 := by
      intro j
      simp only [c, X0, MvPowerSeries.coeff_X_pow]
      simp [Finsupp.single_left_inj (a := i0)]
      sorry
    simp [hc, Finset.sum_ite_eq, hi] at this
    exact this
  let aug : A →ₐ[k] k := AlgHom.mk (MvPowerSeries.constantCoeff : A →+* k) (fun r => by simp)
  let χ : A ⊗[k] A →ₐ[k] k := Algebra.TensorProduct.lift aug aug (fun _ _ => Commute.all _ _)
  have χt : ∀ a b, χ (a ⊗ₜ b) = aug a * aug b := by
    intro a b; simp [χ]
  haveI : IsLocalRing (A ⊗[k] A) := RingEquiv.isLocalRing e.symm.toRingEquiv
  have hsurj : Function.Surjective (χ : A ⊗[k] A →+* k) := by
    intro r
    refine ⟨algebraMap k A r ⊗ₜ 1, ?_⟩
    simp [χt, aug]
  have hmax := RingHom.ker_isMaximal_of_surjective (χ : A ⊗[k] A →+* k) hsurj
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hnu : ¬ IsUnit (1 - (X0 ⊗ₜ[k] X0) : A ⊗[k] A) := by
    rintro ⟨w, hw⟩
    have hw' : (1 - (X0 ⊗ₜ[k] X0)) * (w⁻¹ : (A ⊗[k] A)ˣ) = 1 := by
      rw [← hw]; exact w.mul_inv
    set v : A ⊗[k] A := (w⁻¹ : (A ⊗[k] A)ˣ)
    have hv : v = 1 + (X0 ⊗ₜ[k] X0) * v := by
      have : v - (X0 ⊗ₜ[k] X0) * v = 1 := by rw [← hw']; ring
      rw [← this]; ring
    obtain ⟨F, hF, hmem⟩ := fin v
    have hall : ∀ i, X0 ^ i ∈ F := fun i => by rw [← key v hv i]; exact hmem _
    let f : ℕ → F := fun i => ⟨X0 ^ i, hall i⟩
    have hli : LinearIndependent k f := by
      apply LinearIndependent.of_comp F.subtype
      exact LI
    exact not_finite ℕ |>.elim (Module.Finite.finite_of_linearIndependent hli) 
  apply hnu
  by_contra hcon
  have hm : (1 - (X0 ⊗ₜ[k] X0) : A ⊗[k] A) ∈ IsLocalRing.maximalIdeal (A ⊗[k] A) := hcon
  rw [← heq] at hm
  have : χ (1 - (X0 ⊗ₜ[k] X0)) = 0 := hm
  rw [map_sub, map_one, χt] at this
  simp [aug, X0] at this

end Problem67
