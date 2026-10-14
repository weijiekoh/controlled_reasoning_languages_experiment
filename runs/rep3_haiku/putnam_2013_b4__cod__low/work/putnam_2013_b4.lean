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
  have hi : ∀ k : C(Icc (0 : ℝ) 1, ℝ), MeasureTheory.Integrable (fun x => k x) := fun k =>
    k.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : ∀ k : Icc (0 : ℝ) 1 → ℝ, Continuous k → MeasureTheory.Integrable k := fun k hk =>
    hk.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- variance is minimal among shifts
  have L : ∀ (h : C(Icc (0 : ℝ) 1, ℝ)) (c : ℝ), Var h ≤ ∫ x, (h x - c) ^ 2 := by
    intro h c
    rw [hVar h]
    have hm : ∫ x, (h x - μ h) = 0 := by
      rw [MeasureTheory.integral_sub (hi h) (MeasureTheory.integrable_const _), MeasureTheory.integral_const, ← hμ h]
      simp
    have key : ∀ x, (h x - c) ^ 2 = (h x - μ h) ^ 2 + 2 * (μ h - c) * (h x - μ h) + (μ h - c) ^ 2 := by
      intro x; ring
    have hI1 : MeasureTheory.Integrable (fun x => (h x - μ h) ^ 2) := hi' _ (by fun_prop)
    have hI2 : MeasureTheory.Integrable (fun x => 2 * (μ h - c) * (h x - μ h)) :=
      (hi' _ (by fun_prop)).const_mul _
    have hI3 : MeasureTheory.Integrable (fun _ : Icc (0 : ℝ) 1 => (μ h - c) ^ 2) := MeasureTheory.integrable_const _
    have hI12 : MeasureTheory.Integrable (fun x => (h x - μ h) ^ 2 + 2 * (μ h - c) * (h x - μ h)) := hI1.add hI2
    have eq : ∫ x, (h x - c) ^ 2 = ∫ x, ((h x - μ h) ^ 2 + 2 * (μ h - c) * (h x - μ h) + (μ h - c) ^ 2) := by
      congr 1; funext x; exact key x
    rw [eq, MeasureTheory.integral_add (hI12) hI3, MeasureTheory.integral_add hI1 hI2, MeasureTheory.integral_const_mul, hm]
    simp
    positivity
  -- bounds on sup norms
  have hfx : ∀ x, |f x| ≤ M f := fun x => (hM f).2 ⟨x, rfl⟩
  have hgx : ∀ x, |g x| ≤ M g := fun x => (hM g).2 ⟨x, rfl⟩
  have hg2 : ∀ x, (g x) ^ 2 ≤ (M g) ^ 2 := fun x => by
    have := hgx x
    nlinarith [abs_nonneg (g x), sq_abs (g x)]
  have hMf0 : 0 ≤ M f := le_trans (abs_nonneg _) (hfx ⟨0, by simp⟩)
  have ha1 : μ f ≤ M f := by
    rw [hμ f]
    have := MeasureTheory.integral_mono (hi f) (MeasureTheory.integrable_const (M f)) (fun x => (abs_le.mp (hfx x)).2)
    simpa using this
  have ha2 : -M f ≤ μ f := by
    rw [hμ f]
    have := MeasureTheory.integral_mono (MeasureTheory.integrable_const (-M f)) (hi f) (fun x => (abs_le.mp (hfx x)).1)
    simpa using this
  have ha : (μ f) ^ 2 ≤ (M f) ^ 2 := by nlinarith
  -- pointwise decomposition
  have hdec : ∀ x, (f x * g x - μ f * μ g) ^ 2
      ≤ 2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2 := fun x => by
    nlinarith [sq_nonneg (((f x - μ f) * g x) - (μ f * (g x - μ g)))]
  have hIa : MeasureTheory.Integrable (fun x => ((f x - μ f) * g x) ^ 2) := hi' _ (by fun_prop)
  have hIb : MeasureTheory.Integrable (fun x => (μ f * (g x - μ g)) ^ 2) := hi' _ (by fun_prop)
  have hIc : MeasureTheory.Integrable (fun x => (g x - μ g) ^ 2) := hi' _ (by fun_prop)
  have hId : MeasureTheory.Integrable (fun x => (f x - μ f) ^ 2) := hi' _ (by fun_prop)
  have hIe : MeasureTheory.Integrable (fun x => (M g) ^ 2 * (f x - μ f) ^ 2) := hId.const_mul _
  have hIf : MeasureTheory.Integrable (fun x => (μ f) ^ 2 * (g x - μ g) ^ 2) := hIc.const_mul _
  have e1 : ∫ x, ((f x - μ f) * g x) ^ 2 ≤ ∫ x, (M g) ^ 2 * (f x - μ f) ^ 2 := by
    apply MeasureTheory.integral_mono hIa hIe
    intro x
    nlinarith [mul_nonneg (sq_nonneg (f x - μ f)) (sub_nonneg.2 (hg2 x))]
  have e2 : ∫ x, (μ f * (g x - μ g)) ^ 2 ≤ ∫ x, (M f) ^ 2 * (g x - μ g) ^ 2 := by
    apply MeasureTheory.integral_mono hIb ((hIc.const_mul _))
    intro x
    have := mul_le_mul_of_nonneg_right ha (sq_nonneg (g x - μ g))
    nlinarith
  have hsq : Var (f * g) ≤ ∫ x, (f x * g x - μ f * μ g) ^ 2 := by
    have := L (f * g) (μ f * μ g)
    simpa using this
  have hsplit : ∫ x, (f x * g x - μ f * μ g) ^ 2
      ≤ ∫ x, (2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2) :=
    MeasureTheory.integral_mono ((hi' _ (by fun_prop))) (hIa.const_mul 2 |>.add (hIb.const_mul 2)) hdec
  have hexp : ∫ x, (2 * ((f x - μ f) * g x) ^ 2 + 2 * (μ f * (g x - μ g)) ^ 2)
      = 2 * (∫ x, ((f x - μ f) * g x) ^ 2) + 2 * (∫ x, (μ f * (g x - μ g)) ^ 2) := by
    rw [MeasureTheory.integral_add (hIa.const_mul 2) (hIb.const_mul 2), MeasureTheory.integral_const_mul 2, MeasureTheory.integral_const_mul 2]
  have hVf : Var f = ∫ x, (f x - μ f) ^ 2 := hVar f
  have hVg : Var g = ∫ x, (g x - μ g) ^ 2 := hVar g
  have hnn : 0 ≤ ∫ x, (g x - μ g) ^ 2 := MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hnf : 0 ≤ ∫ x, (f x - μ f) ^ 2 := MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hb : ∫ x, (μ f * (g x - μ g)) ^ 2 = (μ f) ^ 2 * ∫ x, (g x - μ g) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; ext x; ring
  have hMg0 : 0 ≤ (M g) ^ 2 := sq_nonneg _
  have hc1 : ∫ x, ((f x - μ f) * g x) ^ 2 ≤ (M g) ^ 2 * Var f := by
    rw [hVf]; linarith [e1, (by rw [← MeasureTheory.integral_const_mul] : ∫ x, (M g) ^ 2 * (f x - μ f) ^ 2 = (M g) ^ 2 * ∫ x, (f x - μ f) ^ 2)]
  have hc2 : ∫ x, (μ f * (g x - μ g)) ^ 2 ≤ (M f) ^ 2 * Var g := by
    rw [hVg]; linarith [e2, (by rw [← MeasureTheory.integral_const_mul] : ∫ x, (M f) ^ 2 * (g x - μ g) ^ 2 = (M f) ^ 2 * ∫ x, (g x - μ g) ^ 2)]
  have hb2 : (μ f) ^ 2 * Var g ≤ (M f) ^ 2 * Var g := mul_le_mul_of_nonneg_right ha (by rw [hVg]; exact hnn)
  rw [hexp] at hsplit
  nlinarith [hc1, hc2, hsq, hsplit, hb2]
