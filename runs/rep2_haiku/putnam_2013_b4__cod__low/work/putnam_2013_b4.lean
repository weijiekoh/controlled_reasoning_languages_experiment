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
open MeasureTheory in
by
  have hP : volume (univ : Set (Icc (0:ℝ) 1)) = 1 := by
    have := (MeasurableEmbedding.subtype_coe (measurableSet_Icc (a := (0:ℝ)) (b := 1))).comap_apply (volume : Measure ℝ) (univ : Set (Icc (0:ℝ) 1))
    have hv : (volume : Measure (Icc (0:ℝ) 1)) = Measure.comap Subtype.val volume := rfl
    have himg : Subtype.val '' (univ : Set (Icc (0:ℝ) 1)) = Icc (0:ℝ) 1 := by
      ext x; simp
    rw [hv, this, himg, Real.volume_Icc]
    simp
  have hint : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ → Integrable φ := by
    intro φ hφ
    exact hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsplit : ∀ (h : Icc (0:ℝ) 1 → ℝ) (c : ℝ), Continuous h →
      ∫ x, (h x - c)^2 = (∫ x, (h x - ∫ y, h y)^2) + ((∫ y, h y) - c)^2 := by
    intro h c hh
    have e : ∀ x, (h x - c)^2 = ((h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) + ((∫ y, h y)-c)^2 := by
      intro x; ring
    have i1 : Integrable (fun x => (h x - ∫ y, h y)^2) := hint _ (by fun_prop)
    have i2 : Integrable (fun x => (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) := hint _ (by fun_prop)
    have i3 : Integrable (fun _ : Icc (0:ℝ) 1 => ((∫ y, h y)-c)^2) := integrable_const _
    have A1 : (∫ x, ((h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) + ((∫ y, h y)-c)^2)
        = (∫ x, ((h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)))
          + ∫ _x : Icc (0:ℝ) 1, ((∫ y, h y)-c)^2 :=
      integral_add (f := fun x => (h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) (g := fun _ => ((∫ y, h y)-c)^2) (i1.add i2) i3
    have A2 : (∫ x, ((h x - ∫ y, h y)^2 + (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)))
        = (∫ x, (h x - ∫ y, h y)^2) + ∫ x, (2*((∫ y, h y)-c)) * (h x - ∫ y, h y) :=
      integral_add (f := fun x => (h x - ∫ y, h y)^2) (g := fun x => (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) i1 i2
    have A3 : (∫ x, (2*((∫ y, h y)-c)) * (h x - ∫ y, h y)) = (2*((∫ y, h y)-c)) * ∫ x, (h x - ∫ y, h y) := by
      rw [integral_const_mul]
    have A4 : (∫ x, (h x - ∫ y, h y)) = (∫ x, h x) - ∫ y, h y := by
      rw [integral_sub (hint _ hh) (integrable_const _), integral_const]
      simp [Measure.real, hP]
    have A5 : (∫ _x : Icc (0:ℝ) 1, ((∫ y, h y)-c)^2) = ((∫ y, h y) - c)^2 := by
      rw [integral_const]; simp [Measure.real, hP]
    have A6 : (∫ x, h x) = ∫ y, h y := rfl
    simp_rw [e]
    rw [A1, A2, A3, A4, A5, A6]
    ring
  have key : ∀ (h : Icc (0:ℝ) 1 → ℝ) (c : ℝ), Continuous h →
      (∫ x, (h x - ∫ y, h y)^2) ≤ ∫ x, (h x - c)^2 := by
    intro h c hh
    rw [hsplit h c hh]
    nlinarith [sq_nonneg ((∫ y, h y) - c)]
  have hMle : ∀ (h : C(Icc (0:ℝ) 1, ℝ)) (x : Icc (0:ℝ) 1), |h x| ≤ M h := fun h x =>
    (hM h).2 (by exact ⟨x, rfl⟩)
  have hMsq : ∀ (h : C(Icc (0:ℝ) 1, ℝ)) (x : Icc (0:ℝ) 1), h x ^ 2 ≤ M h ^ 2 := by
    intro h x
    have h1 := hMle h x
    have h0 : (0:ℝ) ≤ |h x| := abs_nonneg _
    nlinarith [sq_abs (h x), abs_nonneg (h x)]
  have hmu : ∀ h : C(Icc (0:ℝ) 1, ℝ), (μ h)^2 ≤ (M h)^2 := by
    intro h
    rw [hμ]
    have h1 : ‖∫ x, h x‖ ≤ M h * (volume (univ : Set (Icc (0:ℝ) 1))).toReal := by
      apply norm_integral_le_of_norm_le_const
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact hMle h x
    rw [hP] at h1
    simp at h1
    nlinarith [sq_abs (∫ x, h x), abs_nonneg (∫ x, h x)]
  have hf := hVar f
  have hg := hVar g
  have hVg : 0 ≤ Var g := by
    rw [hg]; exact integral_nonneg (fun x => sq_nonneg _)
  have step1 : Var (f*g) ≤ ∫ x, (f x * g x - μ f * μ g)^2 := by
    rw [hVar (f*g), hμ (f*g)]
    simp only [ContinuousMap.mul_apply]
    exact key (fun x => f x * g x) (μ f * μ g) (by fun_prop)
  have step2 : (∫ x, (f x * g x - μ f * μ g)^2) ≤
      ∫ x, (2*(((f x - μ f)^2) * g x^2) + 2*(μ f)^2 * (g x - μ g)^2) := by
    apply integral_mono (hint _ (by fun_prop)) (hint _ (by fun_prop))
    intro x
    have e : f x * g x - μ f * μ g = (f x - μ f) * g x + μ f * (g x - μ g) := by ring
    show (f x * g x - μ f * μ g)^2 ≤ 2*(((f x - μ f)^2) * g x^2) + 2*(μ f)^2 * (g x - μ g)^2
    rw [e]
    nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
  have step3 : (∫ x, (2*(((f x - μ f)^2) * g x^2) + 2*(μ f)^2 * (g x - μ g)^2))
      = 2 * (∫ x, ((f x - μ f)^2) * g x^2) + 2*(μ f)^2 * Var g := by
    have i1 : Integrable (fun x => 2*(((f x - μ f)^2) * g x^2)) := hint _ (by fun_prop)
    have i2 : Integrable (fun x => 2*(μ f)^2 * (g x - μ g)^2) := hint _ (by fun_prop)
    have A1 : (∫ x, (2*(((f x - μ f)^2) * g x^2) + 2*(μ f)^2 * (g x - μ g)^2))
        = (∫ x, 2*(((f x - μ f)^2) * g x^2)) + ∫ x, 2*(μ f)^2 * (g x - μ g)^2 :=
      integral_add (f := fun x => 2*(((f x - μ f)^2) * g x^2)) (g := fun x => 2*(μ f)^2 * (g x - μ g)^2) i1 i2
    have A2 : (∫ x, 2*(((f x - μ f)^2) * g x^2)) = 2 * ∫ x, ((f x - μ f)^2) * g x^2 :=
      integral_const_mul _ _
    have A3 : (∫ x, 2*(μ f)^2 * (g x - μ g)^2) = 2*(μ f)^2 * ∫ x, (g x - μ g)^2 :=
      integral_const_mul _ _
    rw [A1, A2, A3, hg]
  have step4 : (∫ x, ((f x - μ f)^2) * g x^2) ≤ M g ^ 2 * Var f := by
    have h1 : (∫ x, ((f x - μ f)^2) * g x^2) ≤ ∫ x, M g ^ 2 * (f x - μ f)^2 := by
      apply integral_mono (hint _ (by fun_prop)) (hint _ (by fun_prop))
      intro x
      have := mul_le_mul_of_nonneg_left (hMsq g x) (sq_nonneg (f x - μ f))
      nlinarith [this]
    have h2 : (∫ x, M g ^ 2 * (f x - μ f)^2) = M g ^ 2 * Var f := by
      rw [integral_const_mul, hf]
    linarith
  have h5 : μ f ^ 2 * Var g ≤ M f ^ 2 * Var g := mul_le_mul_of_nonneg_right (hmu f) hVg
  nlinarith [step1, step2, step3, step4, h5]
