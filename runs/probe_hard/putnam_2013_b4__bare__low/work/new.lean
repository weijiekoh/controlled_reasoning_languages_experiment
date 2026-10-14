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
  ·
    haveI : IsProbabilityMeasure (volume : Measure (Icc (0:ℝ) 1)) := by
      constructor; simp
    have hint : ∀ h : C(Icc (0 : ℝ) 1, ℝ), Integrable (fun x => h x) := fun h =>
      h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have key : ∀ (h : C(Icc (0 : ℝ) 1, ℝ)) (c : ℝ), Var h ≤ ∫ x, (h x - c) ^ 2 := by
      intro h c
      have h1 : Integrable (fun x => h x) := hint h
      have h2 : Integrable (fun x => (h x)^2) := hint (h*h) |>.congr (by simp [sq])
      have e1 : ∫ x, (h x - μ h) ^ 2 = (∫ x, (h x)^2) - (μ h)^2 := by
        have : ∀ x, (h x - μ h) ^ 2 = (h x)^2 - 2 * μ h * h x + (μ h)^2 := fun x => by ring
        simp_rw [this]
        have i3 : Integrable (fun x => (h x)^2 - 2 * μ h * h x) := h2.sub (h1.const_mul _)
        rw [integral_add i3 (integrable_const _), integral_sub h2 (h1.const_mul _),
          integral_const_mul, ← hμ]
        simp; ring
      have e2 : ∫ x, (h x - c) ^ 2 = (∫ x, (h x)^2) - 2 * c * μ h + c^2 := by
        have : ∀ x, (h x - c) ^ 2 = (h x)^2 - 2 * c * h x + c^2 := fun x => by ring
        simp_rw [this]
        have i3 : Integrable (fun x => (h x)^2 - 2 * c * h x) := h2.sub (h1.const_mul _)
        rw [integral_add i3 (integrable_const _), integral_sub h2 (h1.const_mul _),
          integral_const_mul, ← hμ]
        simp
      rw [hVar, e1, e2]; nlinarith [sq_nonneg (μ h - c)]
    have bf : ∀ x, (f x)^2 ≤ (M f)^2 := fun x => by
      have := (hM f).2 ⟨x, rfl⟩
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
    have bg : ∀ x, (g x)^2 ≤ (M g)^2 := fun x => by
      have := (hM g).2 ⟨x, rfl⟩
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
    have muf : (μ f)^2 ≤ (M f)^2 := by
      have : |μ f| ≤ M f := by
        rw [hμ]
        have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Icc (0:ℝ) 1))) (f := fun x => f x) (C := M f) (Filter.Eventually.of_forall fun x => by simpa using (hM f).2 ⟨x, rfl⟩)
        simpa using this
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
    have vf : Integrable (fun x => (f x - μ f)^2) := hint ((f - .const _ (μ f)) * (f - .const _ (μ f))) |>.congr (by simp [sq])
    have vg : Integrable (fun x => (g x - μ g)^2) := hint ((g - .const _ (μ g)) * (g - .const _ (μ g))) |>.congr (by simp [sq])
    have hv : ∀ h : C(Icc (0 : ℝ) 1, ℝ), Var h = ∫ x, (h x - μ h)^2 := hVar
    refine (key (f*g) (μ f * μ g)).trans ?_
    have pt : ∀ x : Icc (0:ℝ) 1, ((f*g) x - μ f * μ g)^2 ≤ 2 * (f x - μ f)^2 * (M g)^2 + 2 * (M f)^2 * (g x - μ g)^2 := by
      intro x
      have : (f*g) x - μ f * μ g = (f x - μ f) * g x + μ f * (g x - μ g) := by simp; ring
      rw [this]
      have a := bg x
      have b := muf
      nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g)), mul_le_mul_of_nonneg_left a (sq_nonneg (f x - μ f)), mul_le_mul_of_nonneg_right b (sq_nonneg (g x - μ g))]
    refine (integral_mono ?_ ?_ pt).trans ?_
    · exact hint ((f*g - .const _ (μ f * μ g)) * (f*g - .const _ (μ f * μ g))) |>.congr (Filter.Eventually.of_forall fun x => by simp [sq])
    · have i1 : Integrable (fun x : Icc (0:ℝ) 1 => 2 * (f x - μ f)^2 * (M g)^2) := by
        simpa [mul_assoc] using (vf.mul_const ((M g)^2)).const_mul 2
      have i2 : Integrable (fun x : Icc (0:ℝ) 1 => 2 * (M f)^2 * (g x - μ g)^2) := by
        simpa [mul_assoc] using (vg.const_mul ((M f)^2)).const_mul 2
      exact i1.add i2
    · have i1 : Integrable (fun x : Icc (0:ℝ) 1 => 2 * (f x - μ f)^2 * (M g)^2) := by
        simpa [mul_assoc] using (vf.mul_const ((M g)^2)).const_mul 2
      have i2 : Integrable (fun x : Icc (0:ℝ) 1 => 2 * (M f)^2 * (g x - μ g)^2) := by
        simpa [mul_assoc] using (vg.const_mul ((M f)^2)).const_mul 2
      rw [integral_add i1 i2]
      have e1 : ∫ x : Icc (0:ℝ) 1, 2 * (f x - μ f)^2 * (M g)^2 = 2 * Var f * (M g)^2 := by
        simp_rw [mul_assoc]; rw [integral_const_mul, integral_mul_const, hv f]
      have e2 : ∫ x : Icc (0:ℝ) 1, 2 * (M f)^2 * (g x - μ g)^2 = 2 * Var g * (M f)^2 := by
        simp_rw [mul_assoc]; rw [integral_const_mul, integral_const_mul, hv g]; ring
      rw [e1, e2]
