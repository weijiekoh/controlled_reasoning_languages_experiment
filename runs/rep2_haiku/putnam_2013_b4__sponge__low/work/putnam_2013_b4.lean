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
  have hint : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ → MeasureTheory.Integrable φ := by
    intro φ hφ
    exact hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)
  have hdec : ∀ (h : C(Icc (0:ℝ) 1, ℝ)) (c : ℝ),
      ∫ x, (h x - c)^2 = (∫ x, (h x - μ h)^2) + (μ h - c)^2 := by
    intro h c
    have hI : MeasureTheory.Integrable (fun x => h x) := hint _ h.continuous
    have hc : Continuous (fun x => h x) := h.continuous
    rw [hμ h]
    have e : ∀ x, (h x - c)^2
        = (h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y) + ((∫ y, h y)-c)^2 := by
      intro x; ring
    simp_rw [e]
    have i1 : MeasureTheory.Integrable (fun x => (h x - ∫ y, h y)^2) :=
      hint _ ((hc.sub continuous_const).pow 2)
    have i2 : MeasureTheory.Integrable (fun x => (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) :=
      hint _ (continuous_const.mul (hc.sub continuous_const))
    have i12 : MeasureTheory.Integrable (fun x => (h x - ∫ y, h y)^2
        + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) := i1.add i2
    rw [MeasureTheory.integral_add i12 (MeasureTheory.integrable_const _),
      MeasureTheory.integral_add i1 i2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub hI (MeasureTheory.integrable_const _)]
    simp
  have hVarnn : ∀ h : C(Icc (0:ℝ) 1, ℝ), 0 ≤ Var h := by
    intro h
    rw [hVar h]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hMb : ∀ h : C(Icc (0:ℝ) 1, ℝ), ∀ x, |h x| ≤ M h := fun h x => (hM h).2 (mem_range_self x)
  have hMμ : ∀ h : C(Icc (0:ℝ) 1, ℝ), (μ h)^2 ≤ (M h)^2 := by
    intro h
    have hb : ‖∫ x, h x‖ ≤ M h * (MeasureTheory.volume (univ : Set (Icc (0:ℝ) 1))).toReal :=
      MeasureTheory.norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]; exact hMb h x))
    have hv : (MeasureTheory.volume (univ : Set (Icc (0:ℝ) 1))).toReal = 1 := by simp
    rw [hv, mul_one] at hb
    have hMn : 0 ≤ M h := le_trans (abs_nonneg _) (hMb h ⟨0, by simp⟩)
    rw [hμ h]
    have hb' : |∫ x, h x| ≤ M h := by simpa [Real.norm_eq_abs] using hb
    nlinarith [abs_nonneg (∫ x, h x), sq_abs (∫ x, h x)]
  have hmain : Var (f * g) ≤ ∫ x, (f x * g x - μ f * μ g)^2 := by
    rw [hVar (f * g)]
    have := hdec (f * g) (μ f * μ g)
    have h0 : 0 ≤ (μ (f * g) - μ f * μ g)^2 := sq_nonneg _
    simp only [ContinuousMap.mul_apply] at this ⊢
    linarith
  have hpt : ∀ x, (f x * g x - μ f * μ g)^2
      ≤ (2 * (M g)^2) * (f x - μ f)^2 + (2 * (μ f)^2) * (g x - μ g)^2 := by
    intro x
    have hgx : (g x)^2 ≤ (M g)^2 := by
      have h1 := hMb g x
      have h2 := le_abs_self (g x)
      have h3 := neg_abs_le (g x)
      have h4 : 0 ≤ M g := le_trans (abs_nonneg _) h1
      nlinarith
    have hA : (f x - μ f)^2 * (g x)^2 ≤ (f x - μ f)^2 * (M g)^2 :=
      mul_le_mul_of_nonneg_left hgx (sq_nonneg _)
    nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
  have hf1 : MeasureTheory.Integrable (fun x => (f x * g x - μ f * μ g)^2) :=
    hint _ (((f.continuous.mul g.continuous).sub continuous_const).pow 2)
  have hR1 : MeasureTheory.Integrable (fun x => (2 * (M g)^2) * (f x - μ f)^2) :=
    hint _ (continuous_const.mul ((f.continuous.sub continuous_const).pow 2))
  have hR2 : MeasureTheory.Integrable (fun x => (2 * (μ f)^2) * (g x - μ g)^2) :=
    hint _ (continuous_const.mul ((g.continuous.sub continuous_const).pow 2))
  have hint3 : ∫ x, (f x * g x - μ f * μ g)^2
      ≤ ∫ x, ((2 * (M g)^2) * (f x - μ f)^2 + (2 * (μ f)^2) * (g x - μ g)^2) :=
    MeasureTheory.integral_mono hf1 (hR1.add hR2) hpt
  rw [MeasureTheory.integral_add hR1 hR2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, ← hVar f, ← hVar g] at hint3
  have hk : (μ f)^2 * Var g ≤ (M f)^2 * Var g :=
    mul_le_mul_of_nonneg_right (hMμ f) (hVarnn g)
  nlinarith
