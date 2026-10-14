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
  classical
  have hcI : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ → MeasureTheory.Integrable φ MeasureTheory.volume := fun φ hφ =>
    hφ.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hint : ∀ h : C(Icc (0 : ℝ) 1, ℝ), MeasureTheory.Integrable h MeasureTheory.volume := fun h => hcI h h.continuous
  have hb : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, -(M h) ≤ h x ∧ h x ≤ M h := by
    intro h x
    have := (hM h).2 ⟨x, rfl⟩
    exact abs_le.1 this
  have hmu : ∀ h : C(Icc (0 : ℝ) 1, ℝ), |μ h| ≤ M h := by
    intro h
    rw [hμ, abs_le]
    constructor
    · have := MeasureTheory.integral_mono (MeasureTheory.integrable_const (-M h)) (hint h) (fun x => (hb h x).1)
      simpa using this
    · have := MeasureTheory.integral_mono (hint h) (MeasureTheory.integrable_const (M h)) (fun x => (hb h x).2)
      simpa using this
  have hvar : ∀ (h : C(Icc (0 : ℝ) 1, ℝ)) (c : ℝ), ∫ x, (h x - μ h) ^ 2 ≤ ∫ x, (h x - c) ^ 2 := by
    intro h c
    have i1 : MeasureTheory.Integrable (fun x => (h x - μ h) ^ 2) MeasureTheory.volume :=
      hcI _ (((h.continuous).sub continuous_const).pow 2)
    have i2 : MeasureTheory.Integrable (fun x => h x) MeasureTheory.volume := hint h
    have e : (fun x => (h x - c) ^ 2) = fun x => ((h x - μ h) ^ 2 + (2 * (μ h - c)) * h x + ((μ h - c) ^ 2 - 2 * (μ h - c) * μ h)) := by
      funext x; ring
    have hA : MeasureTheory.Integrable (fun x => (h x - μ h) ^ 2 + (2 * (μ h - c)) * h x) MeasureTheory.volume :=
      i1.add (i2.const_mul _)
    have hK : MeasureTheory.Integrable (fun _ : Icc (0:ℝ) 1 => (μ h - c) ^ 2 - 2 * (μ h - c) * μ h) MeasureTheory.volume :=
      MeasureTheory.integrable_const _
    have hm : ∫ x, h x = μ h := (hμ h).symm
    have s1 := MeasureTheory.integral_add hA hK
    have s2 := MeasureTheory.integral_add i1 (i2.const_mul (2 * (μ h - c)))
    have s3 : ∫ x, (2 * (μ h - c)) * h x = (2 * (μ h - c)) * μ h := by
      rw [MeasureTheory.integral_const_mul, hm]
    have s4 : ∫ _x : Icc (0:ℝ) 1, ((μ h - c) ^ 2 - 2 * (μ h - c) * μ h) = (μ h - c) ^ 2 - 2 * (μ h - c) * μ h := by
      simp
    have J : ∫ x, (h x - c) ^ 2 = (∫ x, (h x - μ h) ^ 2) + (μ h - c) ^ 2 := by
      rw [e, s1, s2, s3, s4]
      ring
    have hJ : ∫ x, (h x - μ h) ^ 2 ≤ ∫ x, (h x - c) ^ 2 := by
      rw [J]; nlinarith [sq_nonneg (μ h - c)]
    exact hJ
  have hpt : ∀ x, (f x * g x - μ f * μ g) ^ 2 ≤ 2 * M g ^ 2 * (f x - μ f) ^ 2 + 2 * M f ^ 2 * (g x - μ g) ^ 2 := by
    intro x
    have hf2 : (f x) ^ 2 ≤ (M f) ^ 2 := by nlinarith [hb f x]
    have hg2 : (g x) ^ 2 ≤ (M g) ^ 2 := by nlinarith [hb g x]
    have hmf2 : (μ f) ^ 2 ≤ (M f) ^ 2 := by
      have := abs_le.1 (hmu f); nlinarith
    have e : f x * g x - μ f * μ g = (f x - μ f) * g x + μ f * (g x - μ g) := by ring
    rw [e]
    have h1 : ((f x - μ f) * g x) ^ 2 ≤ 2 * M g ^ 2 * (f x - μ f) ^ 2 := by
      have : ((f x - μ f) * g x) ^ 2 = (f x - μ f) ^ 2 * (g x) ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (f x - μ f)]
    have h2 : (μ f * (g x - μ g)) ^ 2 ≤ 2 * M f ^ 2 * (g x - μ g) ^ 2 := by
      have : (μ f * (g x - μ g)) ^ 2 = (μ f) ^ 2 * (g x - μ g) ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (g x - μ g)]
    nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
  have hsum : ∀ x, 2 * M g ^ 2 * (f x - μ f) ^ 2 + 2 * M f ^ 2 * (g x - μ g) ^ 2 =
      (2 * M g ^ 2) * (f x - μ f) ^ 2 + (2 * M f ^ 2) * (g x - μ g) ^ 2 := fun x => by ring
  have ci : ∀ φ : C(Icc (0 : ℝ) 1, ℝ), MeasureTheory.Integrable (fun x => (φ x - μ φ) ^ 2) MeasureTheory.volume :=
    fun φ => hcI _ (((φ.continuous).sub continuous_const).pow 2)
  have hfg : Var (f * g) ≤ ∫ x, (f x * g x - μ f * μ g) ^ 2 := by
    rw [hVar]
    have := hvar (f * g) (μ f * μ g)
    simpa only [ContinuousMap.mul_apply] using this
  have hprod : MeasureTheory.Integrable (fun x => (f x * g x - μ f * μ g) ^ 2) MeasureTheory.volume :=
    hcI _ ((((f.continuous.mul g.continuous)).sub continuous_const).pow 2)
  calc Var (f * g) ≤ ∫ x, (f x * g x - μ f * μ g) ^ 2 := hfg
    _ ≤ ∫ x, ((2 * M g ^ 2) * (f x - μ f) ^ 2 + (2 * M f ^ 2) * (g x - μ g) ^ 2) :=
        MeasureTheory.integral_mono hprod (((ci f).const_mul _).add ((ci g).const_mul _)) (fun x => by
          have := hpt x; rw [hsum x] at this; linarith)
    _ = 2 * Var f * M g ^ 2 + 2 * Var g * M f ^ 2 := by
        rw [MeasureTheory.integral_add ((ci f).const_mul _) ((ci g).const_mul _), MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul, hVar f, hVar g]
        ring
