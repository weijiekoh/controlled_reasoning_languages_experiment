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
  have hint : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ → MeasureTheory.Integrable φ :=
    fun φ hφ => hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgM : ∀ x, |g x| ≤ M g := fun x => (hM g).2 ⟨x, rfl⟩
  have hfM : ∀ x, |f x| ≤ M f := fun x => (hM f).2 ⟨x, rfl⟩
  have hfc : Continuous (fun x => f x) := f.continuous
  have hgc : Continuous (fun x => g x) := g.continuous
  have hA : |∫ x, f x| ≤ M f := by
    have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := MeasureTheory.volume)
      (f := fun x => f x) (C := M f)
      (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hfM x))
    simpa [Real.norm_eq_abs] using this
  have hA2 : (∫ x, f x)^2 ≤ (M f)^2 := by
    nlinarith [abs_nonneg (∫ x, f x), sq_abs (∫ x, f x), hA]
  have hfa : Var f = ∫ x, (f x - ∫ y, f y)^2 := by rw [hVar, hμ]
  have hgb : Var g = ∫ x, (g x - ∫ y, g y)^2 := by rw [hVar, hμ]
  have hVg : 0 ≤ Var g := by
    rw [hgb]; exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hfgmu : Var (f * g) = ∫ x, (f x * g x - ∫ y, f y * g y)^2 := by
    rw [hVar, hμ]; simp only [ContinuousMap.mul_apply]
  have hpc : Continuous (fun x => f x * g x) := hfc.mul hgc
  set a := ∫ x, f x with ha
  set b := ∫ x, g x with hb
  set m := ∫ x, f x * g x with hm
  have hI0 : ∫ x, (f x * g x - m) = 0 := by
    rw [MeasureTheory.integral_sub (hint _ hpc) (MeasureTheory.integrable_const _),
      MeasureTheory.integral_const]
    simp [hm]
  have h1 : Var (f * g) ≤ ∫ x, (f x * g x - a * b)^2 := by
    rw [hfgmu]
    have key : ∀ x, (f x * g x - a * b)^2
        = (f x * g x - m)^2 + (2 * (m - a * b)) * (f x * g x - m) + (m - a * b)^2 := by
      intro x; ring
    have i1 : MeasureTheory.Integrable (fun x => (f x * g x - m)^2) :=
      hint _ ((hpc.sub continuous_const).pow 2)
    have i2 : MeasureTheory.Integrable (fun x => (2 * (m - a * b)) * (f x * g x - m)) :=
      hint _ ((hpc.sub continuous_const).const_mul _)
    have i3 : MeasureTheory.Integrable (fun x => (f x * g x - m)^2 + 2 * (m - a * b) * (f x * g x - m)) := i1.add i2
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)]
    rw [MeasureTheory.integral_add i3 (MeasureTheory.integrable_const _),
      MeasureTheory.integral_add i1 i2, MeasureTheory.integral_const_mul, hI0,
      MeasureTheory.integral_const]
    have hv : MeasureTheory.volume.real (univ : Set (Icc (0:ℝ) 1)) = 1 := by simp
    simp [hv]
    positivity
  have pw : ∀ x, (f x * g x - a * b)^2 ≤ 2 * (M g)^2 * (f x - a)^2 + 2 * a^2 * (g x - b)^2 := by
    intro x
    have hg2 : (g x)^2 ≤ (M g)^2 := by
      have := abs_le.mp (hgM x); nlinarith
    have e : f x * g x - a * b = (f x - a) * g x + a * (g x - b) := by ring
    rw [e]
    nlinarith [sq_nonneg ((f x - a) * g x - a * (g x - b)),
      mul_nonneg (sq_nonneg (f x - a)) (sub_nonneg.mpr hg2)]
  have h2 : ∫ x, (f x * g x - a * b)^2
      ≤ ∫ x, (2 * (M g)^2 * (f x - a)^2 + 2 * a^2 * (g x - b)^2) := by
    apply MeasureTheory.integral_mono (hint _ ((hpc.sub continuous_const).pow 2))
    · exact hint _ ((((hfc.sub continuous_const).pow 2).const_mul _).add
        (((hgc.sub continuous_const).pow 2).const_mul _))
    · exact pw
  have h3 : ∫ x, (2 * (M g)^2 * (f x - a)^2 + 2 * a^2 * (g x - b)^2)
      = 2 * (M g)^2 * Var f + 2 * a^2 * Var g := by
    have j1 : MeasureTheory.Integrable (fun x => 2 * (M g)^2 * (f x - a)^2) :=
      hint _ (((hfc.sub continuous_const).pow 2).const_mul _)
    have j2 : MeasureTheory.Integrable (fun x => 2 * a^2 * (g x - b)^2) :=
      hint _ (((hgc.sub continuous_const).pow 2).const_mul _)
    rw [MeasureTheory.integral_add j1 j2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hfa, hgb]
  have h4 : 2 * a^2 * Var g ≤ 2 * (M f)^2 * Var g := by
    nlinarith [mul_le_mul_of_nonneg_left hA2 hVg]
  nlinarith [h1, h2, h3, h4]
