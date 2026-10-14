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
  have hint : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ → MeasureTheory.Integrable φ MeasureTheory.volume := fun φ hφ =>
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound : ∀ h : C(Icc (0:ℝ) 1, ℝ), ∀ x, |h x| ≤ M h := fun h x => (hM h).2 ⟨x, rfl⟩
  have hvol : ∀ h : C(Icc (0:ℝ) 1, ℝ), |μ h| ≤ M h := by
    intro h
    rw [hμ h]
    have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := (MeasureTheory.volume : MeasureTheory.Measure (Icc (0:ℝ) 1)))
      (f := fun x => h x) (C := M h)
      (Filter.Eventually.of_forall (fun x => by simpa using hbound h x))
    simp [MeasureTheory.Measure.real] at this
    linarith
  have key : ∀ (h : C(Icc (0:ℝ) 1, ℝ)) (c : ℝ), ∫ x, (h x - μ h)^2 ≤ ∫ x, (h x - c)^2 := by
    intro h c
    rw [hμ h]
    have hI1 : MeasureTheory.Integrable (fun x : Icc (0:ℝ) 1 => h x) MeasureTheory.volume := hint (fun x : Icc (0:ℝ) 1 => h x) h.continuous
    have hI2 : MeasureTheory.Integrable (fun x : Icc (0:ℝ) 1 => (h x - ∫ y, h y)^2) MeasureTheory.volume :=
      hint (fun x : Icc (0:ℝ) 1 => (h x - ∫ y, h y)^2) (by have := h.continuous; fun_prop)
    have hI3 : MeasureTheory.Integrable (fun x : Icc (0:ℝ) 1 => (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) MeasureTheory.volume :=
      hint (fun x : Icc (0:ℝ) 1 => (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) (by have := h.continuous; fun_prop)
    have hI4 : MeasureTheory.Integrable (fun _ : Icc (0:ℝ) 1 => ((∫ y, h y)-c)^2) MeasureTheory.volume :=
      hint (fun _ : Icc (0:ℝ) 1 => ((∫ y, h y)-c)^2) continuous_const
    have hIs : MeasureTheory.Integrable (fun x : Icc (0:ℝ) 1 => (h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) MeasureTheory.volume :=
      hI2.add hI3
    have e1 : ∫ x, (h x - c)^2 = (∫ x, ((h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y))) + ∫ _x : Icc (0:ℝ) 1, ((∫ y, h y)-c)^2 := by
      rw [← MeasureTheory.integral_add hIs hI4]
      congr 1; ext x; ring
    have e2 : ∫ x, (h x - ∫ y, h y) = 0 := by
      rw [MeasureTheory.integral_sub hI1 (MeasureTheory.integrable_const _), MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real]
    have e3 : (∫ x, ((h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y))) = ∫ x, (h x - ∫ y, h y)^2 := by
      rw [MeasureTheory.integral_add hI2 hI3, MeasureTheory.integral_const_mul, e2]
      ring
    rw [e1, e3, MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real]
    positivity
  have hsq : ∀ (h : C(Icc (0:ℝ) 1, ℝ)), 0 ≤ Var h := by
    intro h
    rw [hVar h]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hA : ∀ x, (f x * g x - μ f * μ g)^2 ≤ 2*(((f x - μ f) * g x)^2) + 2*((μ f)^2 * (g x - μ g)^2) := by
    intro x
    nlinarith [sq_nonneg (((f x - μ f) * g x) - μ f * (g x - μ g))]
  have hfI : MeasureTheory.Integrable (fun x : Icc (0:ℝ) 1 => ((f x - μ f) * g x)^2) MeasureTheory.volume :=
    hint (fun x : Icc (0:ℝ) 1 => ((f x - μ f) * g x)^2) (by have := f.continuous; have := g.continuous; fun_prop)
  have hgI : MeasureTheory.Integrable (fun x : Icc (0:ℝ) 1 => (μ f)^2 * (g x - μ g)^2) MeasureTheory.volume :=
    hint (fun x : Icc (0:ℝ) 1 => (μ f)^2 * (g x - μ g)^2) (by have := g.continuous; fun_prop)
  have hB : ∫ x, ((f x - μ f) * g x)^2 ≤ (M g)^2 * Var f := by
    rw [hVar f, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono hfI
      (hint (fun x : Icc (0:ℝ) 1 => (M g)^2 * (f x - μ f)^2) (by have := f.continuous; fun_prop))
    intro x
    dsimp only
    have hg2 : (g x)^2 ≤ (M g)^2 := by nlinarith [hbound g x, abs_nonneg (g x), sq_abs (g x)]
    have := mul_le_mul_of_nonneg_left hg2 (sq_nonneg (f x - μ f))
    nlinarith [this]
  have hC : ∫ x, (μ f)^2 * (g x - μ g)^2 = (μ f)^2 * Var g := by
    rw [hVar g, MeasureTheory.integral_const_mul]
  have hmf : (μ f)^2 ≤ (M f)^2 := by
    have := hvol f
    nlinarith [abs_nonneg (μ f), sq_abs (μ f)]
  have hfg : Var (f*g) ≤ ∫ x, (f x * g x - μ f * μ g)^2 := by
    have := key (f*g) (μ f * μ g)
    rw [hVar (f*g)]
    simpa only [ContinuousMap.mul_apply] using this
  have hsplit : ∫ x, (2*(((f x - μ f) * g x)^2) + 2*((μ f)^2 * (g x - μ g)^2))
      = 2 * (∫ x, ((f x - μ f) * g x)^2) + 2 * ((μ f)^2 * Var g) := by
    rw [MeasureTheory.integral_add (hfI.const_mul 2) (hgI.const_mul 2)]
    simp only [MeasureTheory.integral_const_mul]
    rw [hVar g]
  have hmono : ∫ x, (f x * g x - μ f * μ g)^2 ≤ ∫ x, (2*(((f x - μ f) * g x)^2) + 2*((μ f)^2 * (g x - μ g)^2)) :=
    MeasureTheory.integral_mono
      (hint (fun x : Icc (0:ℝ) 1 => (f x * g x - μ f * μ g)^2) (by have := f.continuous; have := g.continuous; fun_prop))
      ((hfI.const_mul 2).add (hgI.const_mul 2)) hA
  have hfinal : (μ f)^2 * Var g ≤ (M f)^2 * Var g :=
    mul_le_mul_of_nonneg_right hmf (hsq g)

  have s1 : 2 * (∫ x, ((f x - μ f) * g x)^2) ≤ 2 * ((M g)^2 * Var f) := by linarith [hB]
  have s2 : 2 * ((μ f)^2 * Var g) ≤ 2 * ((M f)^2 * Var g) := by linarith [hfinal]
  calc Var (f*g) ≤ ∫ x, (f x * g x - μ f * μ g)^2 := hfg
    _ ≤ ∫ x, (2*(((f x - μ f) * g x)^2) + 2*((μ f)^2 * (g x - μ g)^2)) := hmono
    _ = 2 * (∫ x, ((f x - μ f) * g x)^2) + 2 * ((μ f)^2 * Var g) := hsplit
    _ ≤ 2 * ((M g)^2 * Var f) + 2 * ((M f)^2 * Var g) := add_le_add s1 s2
    _ = 2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 := by ring
