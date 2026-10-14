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
    Var (f * g) ≤ 2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 :=
by
  open MeasureTheory in
  (
  have hvol : (volume : Measure (Icc (0 : ℝ) 1)) univ = 1 := by
    have hE : MeasurableEmbedding (Subtype.val : Icc (0 : ℝ) 1 → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Icc
    have hv : (volume : Measure (Icc (0 : ℝ) 1)) = (volume : Measure ℝ).comap Subtype.val := rfl
    rw [hv, hE.comap_apply]
    have : (Subtype.val : Icc (0 : ℝ) 1 → ℝ) '' univ = Icc 0 1 := by
      ext x; simp
    rw [this, Real.volume_Icc]; simp
  have hcont : ∀ φ : Icc (0 : ℝ) 1 → ℝ, Continuous φ → Integrable φ volume :=
    fun φ hφ => hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, |h x| ≤ M h := fun h x => (hM h).2 ⟨x, rfl⟩
  have hshift : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ c : ℝ,
      ∫ x, (h x - c) ^ 2 = (∫ x, (h x - ∫ y, h y) ^ 2) + ((∫ y, h y) - c) ^ 2 := by
    intro h c
    set m := ∫ y, h y with hm
    have e : ∀ x, (h x - c) ^ 2 = ((h x - m) ^ 2 + (2 * (m - c)) * h x - (m - c) * (c + m)) := by
      intro x; ring
    have i1 : Integrable (fun x => (h x - m) ^ 2) volume :=
      hcont _ (by fun_prop)
    have i2 : Integrable (fun x => (2 * (m - c)) * h x) volume :=
      hcont _ (by fun_prop)
    have i3 : Integrable (fun _ : Icc (0 : ℝ) 1 => (m - c) * (c + m)) volume :=
      hcont _ continuous_const
    have s1 : ∫ x, (h x - c) ^ 2
        = ∫ x, ((h x - m) ^ 2 + (2 * (m - c)) * h x - (m - c) * (c + m)) :=
          integral_congr_ae (Filter.Eventually.of_forall e)
    have s2 : ∫ x, ((h x - m) ^ 2 + (2 * (m - c)) * h x - (m - c) * (c + m))
        = (∫ x, (h x - m) ^ 2) + (2 * (m - c)) * (∫ x, h x) - (m - c) * (c + m) := by
      rw [integral_sub, integral_add, integral_const_mul]
      · simp [integral_const, measureReal_def, hvol]
      all_goals exact hcont _ (by fun_prop)
    rw [s1, s2, ← hm]
    ring
  have hmuabs : ∀ h : C(Icc (0 : ℝ) 1, ℝ), (∫ y, h y) ^ 2 ≤ M h ^ 2 := by
    intro h
    have : ‖∫ y, h y‖ ≤ M h * Measure.real (volume : Measure (Icc (0 : ℝ) 1)) univ := by
      apply norm_integral_le_of_norm_le_const
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]; exact hbd h x
    rw [measureReal_def, hvol] at this
    simp only [ENNReal.toReal_one, mul_one] at this
    have h2 : |∫ y, h y| ≤ M h := by rwa [← Real.norm_eq_abs]
    nlinarith [abs_nonneg (∫ y, h y), sq_abs (∫ y, h y), (hM h).1]
  have hsq : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, h x ^ 2 ≤ M h ^ 2 := by
    intro h x
    nlinarith [abs_nonneg (h x), sq_abs (h x), hbd h x]
  have hfg : ∀ x, (f * g) x = f x * g x := fun x => ContinuousMap.mul_apply f g x
  have key : ∫ x, (f x * g x - (∫ y, f y) * (∫ y, g y)) ^ 2 ≤
      2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 := by
    have pw : ∀ x, (f x * g x - (∫ y, f y) * (∫ y, g y)) ^ 2 ≤
        2 * (M g ^ 2 * (f x - ∫ y, f y) ^ 2) + 2 * (M f ^ 2 * (g x - ∫ y, g y) ^ 2) := by
      intro x
      have hx1 : (g x) ^ 2 ≤ M g ^ 2 := hsq g x
      have hx2 : (f x - ∫ y, f y) ^ 2 * g x ^ 2 ≤ M g ^ 2 * (f x - ∫ y, f y) ^ 2 := by
        nlinarith [sq_nonneg (f x - ∫ y, f y)]
      have hx3 : (∫ y, f y) ^ 2 * (g x - ∫ y, g y) ^ 2 ≤ M f ^ 2 * (g x - ∫ y, g y) ^ 2 :=
        mul_le_mul_of_nonneg_right (hmuabs f) (sq_nonneg _)
      nlinarith [sq_nonneg ((f x - ∫ y, f y) * g x - (∫ y, f y) * (g x - ∫ y, g y))]
    have hI1 : Integrable (fun x => M g ^ 2 * (f x - ∫ y, f y) ^ 2) volume :=
      hcont _ (by fun_prop)
    have hI2 : Integrable (fun x => M f ^ 2 * (g x - ∫ y, g y) ^ 2) volume :=
      hcont _ (by fun_prop)
    have hI0 : Integrable (fun x => (f x * g x - (∫ y, f y) * (∫ y, g y)) ^ 2) volume :=
      hcont _ (by fun_prop)
    calc ∫ x, (f x * g x - (∫ y, f y) * (∫ y, g y)) ^ 2
        ≤ ∫ x, (2 * (M g ^ 2 * (f x - ∫ y, f y) ^ 2) + 2 * (M f ^ 2 * (g x - ∫ y, g y) ^ 2)) :=
          integral_mono hI0 ((hI1.const_mul 2).add (hI2.const_mul 2)) pw
      _ = 2 * (M g ^ 2 * ∫ x, (f x - ∫ y, f y) ^ 2) + 2 * (M f ^ 2 * ∫ x, (g x - ∫ y, g y) ^ 2) := by
          rw [integral_add ((hI1.const_mul 2)) ((hI2.const_mul 2)),
            integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
      _ = 2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 := by
          rw [hVar, hVar, hμ, hμ]; ring
  have h1 := hshift (f * g) ((∫ y, f y) * (∫ y, g y))
  have h2 : ∫ x, ((f * g) x - (∫ y, f y) * (∫ y, g y)) ^ 2
      = ∫ x, (f x * g x - (∫ y, f y) * (∫ y, g y)) ^ 2 := by
    simp only [ContinuousMap.mul_apply]
  have h3 : Var (f * g) = ∫ x, ((f * g) x - ∫ y, (f * g) y) ^ 2 := by
    rw [hVar, hμ]
  have h4 := sq_nonneg ((∫ y, (f * g) y) - (∫ y, f y) * (∫ y, g y))
  linarith [h1, h2, h3, h4, key]
  )
