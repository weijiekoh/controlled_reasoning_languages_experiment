import Mathlib

open Function Set MeasureTheory

theorem putnam_2013_b4
    (μ Var M : C(Icc (0 : ℝ) 1, ℝ) → ℝ)
    (hμ : ∀ f, μ f = ∫ x, f x)
    (hVar : ∀ f, Var f = ∫ x, (f x - μ f) ^ 2)
    (hM : ∀ f : C(Icc (0 : ℝ) 1, ℝ), IsGreatest (range <| abs ∘ f) (M f))
    (f g : C(Icc (0 : ℝ) 1, ℝ)) :
    Var (f * g) ≤ 2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 := by
  have hint : ∀ φ : Icc (0 : ℝ) 1 → ℝ, Continuous φ → Integrable φ := by
    intro φ hφ
    exact hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, h x ^ 2 ≤ (M h) ^ 2 := by
    intro h x
    have h1 := (hM h).2 ⟨x, rfl⟩
    have h2 : (abs ∘ h) x = |h x| := rfl
    simp only [h2] at h1
    have := abs_nonneg (h x)
    have := sq_abs (h x)
    nlinarith
  have hvol : volume (univ : Set (Icc (0 : ℝ) 1)) = 1 := measure_univ
  have hreal : volume.real (univ : Set (Icc (0 : ℝ) 1)) = 1 := by
    simp [Measure.real, hvol]
  -- variance minimization
  have hmin : ∀ F : C(Icc (0 : ℝ) 1, ℝ), ∀ c : ℝ,
      ∫ x, (F x - μ F) ^ 2 ≤ ∫ x, (F x - c) ^ 2 := by
    intro F c
    have hF : Continuous (fun x => F x) := F.continuous
    have hI1 : Integrable (fun x => F x) := hint _ hF
    have hI2 : Integrable (fun x => (F x - μ F) ^ 2) :=
      hint _ (by fun_prop)
    have hz : ∫ x, (F x - μ F) = 0 := by
      rw [integral_sub hI1 (integrable_const _), integral_const, hμ F, hreal]
      simp
    have hexp : ∀ x, (F x - c) ^ 2 = (F x - μ F) ^ 2 + (2 * (μ F - c)) * (F x - μ F) + (μ F - c) ^ 2 := by
      intro x; ring
    have hI4 : Integrable (fun x => (F x - μ F) ^ 2 + (2 * (μ F - c)) * (F x - μ F)) :=
      hI2.add ((hint _ (by fun_prop)).const_mul _)
    have key : ∫ x, (F x - c) ^ 2 = (∫ x, (F x - μ F) ^ 2) + (μ F - c) ^ 2 := by
      simp_rw [hexp]
      rw [integral_add hI4 (integrable_const _), integral_add hI2 ((hint _ (by fun_prop)).const_mul _),
        integral_const_mul, hz, integral_const, hreal]
      simp
    rw [key]
    have := sq_nonneg (μ F - c)
    linarith
  -- bound on |∫ f|
  have hmu : ∀ h : C(Icc (0 : ℝ) 1, ℝ), (μ h) ^ 2 ≤ (M h) ^ 2 := by
    intro h
    have h1 : ‖∫ x, h x‖ ≤ M h * volume.real (univ : Set (Icc (0 : ℝ) 1)) := by
      apply norm_integral_le_of_norm_le_const
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact (hM h).2 ⟨x, rfl⟩
    rw [hreal, mul_one] at h1
    rw [hμ h]
    have h3 : (∫ x, h x) ^ 2 = ‖∫ x, h x‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [h3]
    have := norm_nonneg (∫ x, h x)
    nlinarith
  -- main estimate
  have hVarnn : 0 ≤ Var g := by
    rw [hVar g]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hpt : ∀ x, (f x * g x - μ f * μ g) ^ 2 ≤
      2 * (M g) ^ 2 * (f x - μ f) ^ 2 + 2 * (μ f) ^ 2 * (g x - μ g) ^ 2 := by
    intro x
    have h1 := mul_le_mul_of_nonneg_left (hbound g x) (sq_nonneg (f x - μ f))
    have h2 := sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))
    have h3 : f x * g x - μ f * μ g = (f x - μ f) * g x + μ f * (g x - μ g) := by ring
    rw [h3]
    nlinarith [h1, h2]
  have hA : Var (f * g) ≤ ∫ x, (f x * g x - μ f * μ g) ^ 2 := by
    rw [hVar (f * g)]
    have := hmin (f * g) (μ f * μ g)
    simpa [ContinuousMap.mul_apply] using this
  have hB : ∫ x, (f x * g x - μ f * μ g) ^ 2 ≤
      ∫ x, (2 * (M g) ^ 2 * (f x - μ f) ^ 2 + 2 * (μ f) ^ 2 * (g x - μ g) ^ 2) := by
    apply integral_mono (hint _ (by fun_prop)) (hint _ (by fun_prop))
    intro x
    exact hpt x
  have hC : ∫ x, (2 * (M g) ^ 2 * (f x - μ f) ^ 2 + 2 * (μ f) ^ 2 * (g x - μ g) ^ 2)
      = 2 * (M g) ^ 2 * Var f + 2 * (μ f) ^ 2 * Var g := by
    rw [integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
      integral_const_mul, integral_const_mul, hVar f, hVar g]
  have hD : 2 * (μ f) ^ 2 * Var g ≤ 2 * (M f) ^ 2 * Var g := by
    have := hmu f
    nlinarith
  have hE : 2 * (M g) ^ 2 * Var f = 2 * Var f * (M g) ^ 2 := by ring
  linarith [hA, hB, hC, hD, hE]
