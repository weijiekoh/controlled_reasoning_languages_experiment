import Mathlib

open Function Set

/--
For any continuous real-valued function $f$ defined on the interval $[0,1]$, let $\mu(f)=\int_0^1 f(x)\,dx,\text{Var}(f)=\int_0^1 (f(x)-\mu(f))^2\,dx,M(f)=\max_{0 \leq x \leq 1} |f(x)|$. Show that if $f$ and $g$ are continuous real-valued functions defined on the interval $[0,1]$, then $\text{Var}(fg) \leq 2\text{Var}(f)M(g)^2+2\text{Var}(g)M(f)^2$.
-/
theorem putnam_2013_b4
    (μ Var M : C(Icc (0 : ℝ) 1, ℝ) → ℝ)
    (hμ : ∀ f, μ f = ∫ x, f x)
    (hVar : ∀ f, Var f = ∫ x, (f x - μ f) ^ 2)
    (hM : ∀ f : C(Icc (0 : ℝ) 1, ℝ), IsGreatest (range <| abs ∘ f) (M f))
    (f g : C(Icc (0 : ℝ) 1, ℝ)) :
    Var (f * g) ≤ 2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 := by
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Icc (0:ℝ) 1)).real univ = 1 := by
    rw [MeasureTheory.Measure.real]
    change ((MeasureTheory.Measure.comap Subtype.val (MeasureTheory.volume : MeasureTheory.Measure ℝ)) univ).toReal = 1
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply,
      Subtype.coe_image_univ, Real.volume_Icc]
    simp
  have hI : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ → MeasureTheory.Integrable φ := fun φ hφ =>
    hφ.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport φ) (subset_univ _))
  have hbound : ∀ (h : C(Icc (0:ℝ) 1, ℝ)) (x : Icc (0:ℝ) 1), |h x| ≤ M h :=
    fun h x => (hM h).2 ⟨x, rfl⟩
  have hbound0 : ∀ h : C(Icc (0:ℝ) 1, ℝ), 0 ≤ M h := by
    intro h
    obtain ⟨x, hx⟩ := (hM h).1
    have h2 : |h x| = M h := hx
    linarith [abs_nonneg (h x)]
  have hint_mean : ∀ h : C(Icc (0:ℝ) 1, ℝ), |μ h| ≤ M h := by
    intro h
    have h1 := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (f := fun x => h x) (C := M h)
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hbound h x))
    rw [hvol, mul_one] at h1
    rw [hμ h, ← Real.norm_eq_abs]
    exact h1
  have hVnn : ∀ h : C(Icc (0:ℝ) 1, ℝ), 0 ≤ Var h := fun h => by
    rw [hVar h]; exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hL : ∀ (h : C(Icc (0:ℝ) 1, ℝ)) (c : ℝ),
      ∫ x, (h x - μ h) ^ 2 ≤ ∫ x, (h x - c) ^ 2 := by
    intro h c
    have e2 : ∫ x, (h x - μ h) = 0 := by
      rw [MeasureTheory.integral_sub (hI _ h.continuous) (MeasureTheory.integrable_const _),
        MeasureTheory.integral_const, hvol, ← hμ h]
      simp
    have key : ∀ x, (h x - c) ^ 2
        = (h x - μ h) ^ 2 + ((μ h - c) ^ 2 + 2 * (μ h - c) * (h x - μ h)) := fun x => by ring
    simp_rw [key]
    rw [MeasureTheory.integral_add (hI _ (by fun_prop)) (by
        exact MeasureTheory.Integrable.add (MeasureTheory.integrable_const _)
          (MeasureTheory.Integrable.const_mul (hI _ (by fun_prop)) _)),
      MeasureTheory.integral_add (MeasureTheory.integrable_const _)
        (MeasureTheory.Integrable.const_mul (hI _ (by fun_prop)) _),
      MeasureTheory.integral_const, MeasureTheory.integral_const_mul, e2, hvol]
    simp only [smul_eq_mul, mul_zero, add_zero, one_mul]
    linarith [sq_nonneg (μ h - c)]
  have hfg : ∀ x, (f * g) x = f x * g x := fun x => rfl
  calc Var (f * g) = ∫ x, ((f * g) x - μ (f * g)) ^ 2 := hVar (f * g)
    _ ≤ ∫ x, ((f * g) x - μ f * μ g) ^ 2 := hL (f * g) _
    _ ≤ ∫ x, (2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2) := by
        apply MeasureTheory.integral_mono (hI _ (by fun_prop)) (hI _ (by fun_prop))
        intro x
        change (f x * g x - μ f * μ g) ^ 2 ≤ 2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2
        nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
    _ = 2 * (∫ x, ((f x - μ f) * g x) ^ 2) + 2 * (∫ x, (μ f * (g x - μ g)) ^ 2) := by
        rw [MeasureTheory.integral_add (hI _ (by fun_prop)) (hI _ (by fun_prop)),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * (M g ^ 2 * Var f) + 2 * (M f ^ 2 * Var g) := by
        have hA : (∫ x, ((f x - μ f) * g x) ^ 2) ≤ M g ^ 2 * Var f := by
          rw [hVar f, ← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_mono (hI _ (by fun_prop)) (hI _ (by fun_prop))
          intro x
          have hg := hbound g x
          have hsq : g x ^ 2 ≤ M g ^ 2 := by
            nlinarith [abs_nonneg (g x), sq_abs (g x)]
          have := mul_le_mul_of_nonneg_left hsq (sq_nonneg (f x - μ f))
          nlinarith [this]
        have hB : (∫ x, (μ f * (g x - μ g)) ^ 2) ≤ M f ^ 2 * Var g := by
          have e : (∫ x, (μ f * (g x - μ g)) ^ 2) = μ f ^ 2 * Var g := by
            rw [hVar g, ← MeasureTheory.integral_const_mul]
            congr 1
            funext x
            ring
          rw [e]
          have hm : μ f ^ 2 ≤ M f ^ 2 := by
            nlinarith [abs_nonneg (μ f), sq_abs (μ f), hint_mean f, hbound0 f]
          exact mul_le_mul_of_nonneg_right hm (hVnn g)
        linarith
    _ = 2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 := by ring
