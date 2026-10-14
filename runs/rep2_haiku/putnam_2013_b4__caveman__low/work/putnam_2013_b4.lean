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
  open MeasureTheory in
  (
    have hvol : volume (univ : Set (Icc (0:ℝ) 1)) = 1 := by
      rw [Measure.Subtype.volume_univ]
      · simp
      · exact measurableSet_Icc.nullMeasurableSet
    have hv1 : volume.real (univ : Set (Icc (0:ℝ) 1)) = 1 := by
      simp [Measure.real, hvol]
    have hint : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ → Integrable φ := fun φ hφ =>
      hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hbd : ∀ h : C(Icc (0:ℝ) 1, ℝ), ∀ x, |h x| ≤ M h := fun h x => (hM h).2 ⟨x, rfl⟩
    have hmbd : ∀ h : C(Icc (0:ℝ) 1, ℝ), |μ h| ≤ M h := by
      intro h
      have := norm_integral_le_of_norm_le_const (μ := volume) (f := ⇑h) (C := M h)
        (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hbd h x))
      rw [hv1, mul_one, ← hμ, Real.norm_eq_abs] at this
      exact this
    -- Var h ≤ ∫ (h - c)^2 for any constant c
    have hV : ∀ h : C(Icc (0:ℝ) 1, ℝ), ∀ c : ℝ, ∫ x, (h x - μ h) ^ 2 ≤ ∫ x, (h x - c) ^ 2 := by
      intro h c
      have hA : Integrable (fun x => (h x - μ h) ^ 2) := hint _ (by fun_prop)
      have hC : Integrable (fun x => (2 * (μ h - c)) * (h x - μ h)) := hint _ (by fun_prop)
      have hD : Integrable (fun _ : Icc (0:ℝ) 1 => (μ h - c) ^ 2) := integrable_const _
      have h1 : ∫ x, (h x - μ h) = 0 := by
        rw [integral_sub (hint _ (by fun_prop)) (integrable_const _), integral_const, hv1, ← hμ]
        simp
      have e2 : ∫ x, (h x - c) ^ 2
          = ∫ x, ((h x - μ h) ^ 2 + (2 * (μ h - c)) * (h x - μ h) + (μ h - c) ^ 2) := by
        congr 1; ext x; ring
      rw [e2, integral_add (f := fun x => (h x - μ h) ^ 2 + 2 * (μ h - c) * (h x - μ h)) (g := fun _ => (μ h - c) ^ 2) (hA.add hC) hD, integral_add hA hC, integral_const_mul, h1,
        integral_const, hv1]
      simp only [smul_eq_mul, mul_zero]
      nlinarith [sq_nonneg (μ h - c)]
    have hvf := hVar f
    have hvg := hVar g
    have hvfg := hVar (f * g)
    have hnn : ∀ h : C(Icc (0:ℝ) 1, ℝ), 0 ≤ ∫ x, (h x - μ h) ^ 2 := fun h =>
      integral_nonneg (fun x => sq_nonneg _)
    have hVg0 := hnn g
    have hmf : (μ f) ^ 2 ≤ (M f) ^ 2 := by
      nlinarith [abs_nonneg (μ f), sq_abs (μ f), hmbd f]
    have hgsq : ∀ x, (g x) ^ 2 ≤ (M g) ^ 2 := fun x => by
      nlinarith [abs_nonneg (g x), sq_abs (g x), hbd g x, abs_nonneg (M g)]
    have hA : ∫ x, ((f x - μ f) * g x) ^ 2 ≤ (M g) ^ 2 * Var f := by
      rw [hvf, ← integral_const_mul]
      apply integral_mono (hint _ (by fun_prop)) (hint _ (by fun_prop))
      intro x
      have := mul_le_mul_of_nonneg_left (hgsq x) (sq_nonneg (f x - μ f))
      nlinarith [this]
    have hB : ∫ x, (μ f * (g x - μ g)) ^ 2 ≤ (M f) ^ 2 * Var g := by
      have e : ∫ x, (μ f * (g x - μ g)) ^ 2 = (μ f) ^ 2 * Var g := by
        rw [hvg, ← integral_const_mul]
        congr 1; ext x; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hmf (by rw [hvg]; exact hVg0)
    have hpt : ∫ x, ((f * g) x - μ (f * g)) ^ 2
        ≤ ∫ x, (2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2) := by
      refine (hV (f * g) (μ f * μ g)).trans (integral_mono ?_ ?_ ?_)
      · exact hint _ (by fun_prop)
      · exact hint _ (by fun_prop)
      · intro x
        simp only [ContinuousMap.mul_apply]
        nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
    have hsum : ∫ x, (2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2)
        = 2 * (∫ x, ((f x - μ f) * g x) ^ 2) + 2 * (∫ x, (μ f * (g x - μ g)) ^ 2) := by
      rw [integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)), integral_const_mul,
        integral_const_mul]
    rw [hvfg]
    nlinarith [hpt, hsum, hA, hB]
  )
