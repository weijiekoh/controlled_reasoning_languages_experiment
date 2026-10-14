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
  open MeasureTheory in by
  have hcI : ∀ φ : Icc (0 : ℝ) 1 → ℝ, Continuous φ → Integrable φ := fun φ hφ =>
    Continuous.integrable_of_hasCompactSupport hφ (HasCompactSupport.of_compactSpace _)
  have hvol : volume.real (univ : Set (Icc (0:ℝ) 1)) = 1 := by
    rw [measureReal_def]; simp
  have hbound : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, |h x| ≤ M h := fun h x => (hM h).2 ⟨x, rfl⟩
  have hVnn : ∀ h : C(Icc (0 : ℝ) 1, ℝ), 0 ≤ Var h := by
    intro h; rw [hVar]; exact integral_nonneg (fun x => sq_nonneg _)
  have hμb : ∀ h : C(Icc (0 : ℝ) 1, ℝ), μ h ^ 2 ≤ M h ^ 2 := by
    intro h
    have hM0 : 0 ≤ M h := le_trans (abs_nonneg _) (hbound h (0 : Icc (0:ℝ) 1))
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Icc (0:ℝ) 1)))
      (f := fun x => h x) (C := M h) (ae_of_all _ (fun x => by
        simpa [Real.norm_eq_abs] using hbound h x))
    rw [← hμ, hvol, mul_one, Real.norm_eq_abs] at this
    have := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    exact this
  have key : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ c : ℝ, Var h ≤ ∫ x, (h x - c) ^ 2 := by
    intro h c
    have hc : Continuous fun x => h x := h.continuous
    have hi0 : Integrable (fun x => h x) := hcI _ hc
    have hi1 : Integrable (fun x => (h x - μ h) ^ 2) :=
      hcI _ (by fun_prop)
    have hi2 : Integrable (fun x => (2 * (μ h - c)) * (h x - μ h)) :=
      hcI _ (by fun_prop)
    have hi3 : Integrable (fun _ : Icc (0:ℝ) 1 => (μ h - c) ^ 2) := integrable_const _
    have e : ∫ x, (h x - c) ^ 2 = ∫ x, (((h x - μ h) ^ 2 + (2 * (μ h - c)) * (h x - μ h)) + (μ h - c) ^ 2) := by
      congr 1; ext x; ring
    have hlin : ∫ x, (h x - μ h) = 0 := by
      rw [integral_sub hi0 (integrable_const _), integral_const, ← hμ, hvol]
      simp
    have hi12 : Integrable (fun x => (h x - μ h) ^ 2 + (2 * (μ h - c)) * (h x - μ h)) := hi1.add hi2
    rw [e, integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul, hlin, integral_const, hvol, ← hVar]
    simp only [smul_eq_mul, one_mul, mul_zero, add_zero]; nlinarith [sq_nonneg (μ h - c)]
  have hpt : ∀ x, (f x * g x - μ f * μ g) ^ 2 ≤ 2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2 := by
    intro x
    nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
  have hA : Integrable (fun x => ((f x - μ f) * g x) ^ 2) := hcI _ (by fun_prop)
  have hB : Integrable (fun x => (μ f * (g x - μ g)) ^ 2) := hcI _ (by fun_prop)
  have hfv : Integrable (fun x => (f x - μ f) ^ 2) := hcI _ (by fun_prop)
  have hgv : Integrable (fun x => (g x - μ g) ^ 2) := hcI _ (by fun_prop)
  have h1 : Var (f * g) ≤ ∫ x, (2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2) := by
    refine le_trans (key (f * g) (μ f * μ g)) ?_
    apply integral_mono (hcI _ (by fun_prop)) ((hA.const_mul 2).add (hB.const_mul 2))
    intro x
    simp only [ContinuousMap.mul_apply]
    exact hpt x
  have hA2 : ∫ x, ((f x - μ f) * g x) ^ 2 ≤ M g ^ 2 * Var f := by
    rw [hVar, ← integral_const_mul]
    apply integral_mono hA (hfv.const_mul _)
    intro x
    have := hbound g x
    have h0 : g x ^ 2 ≤ M g ^ 2 := by
      have := abs_le.mp this
      nlinarith [abs_nonneg (g x)]
    nlinarith [sq_nonneg (f x - μ f)]
  have hB2 : ∫ x, (μ f * (g x - μ g)) ^ 2 = μ f ^ 2 * Var g := by
    rw [hVar, ← integral_const_mul]
    congr 1; ext x; ring
  rw [integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul, integral_const_mul] at h1
  have hB3 : μ f ^ 2 * Var g ≤ M f ^ 2 * Var g := mul_le_mul_of_nonneg_right (hμb f) (hVnn g)
  have hB4 : ∫ x, (μ f * (g x - μ g)) ^ 2 ≤ M f ^ 2 * Var g := by rw [hB2]; exact hB3
  nlinarith [hA2, hB4, h1]
