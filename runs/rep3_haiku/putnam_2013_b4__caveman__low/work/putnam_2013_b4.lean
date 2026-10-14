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
  classical
  have hvol : MeasureTheory.volume (univ : Set (Icc (0:ℝ) 1)) = 1 := by
    rw [MeasureTheory.Measure.Subtype.volume_univ (by exact measurableSet_Icc.nullMeasurableSet)]
    simp
  have hI : ∀ φ : Icc (0:ℝ) 1 → ℝ, Continuous φ →
      MeasureTheory.Integrable φ MeasureTheory.volume :=
    fun φ hφ => hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconst : ∀ c : ℝ, (∫ _x : Icc (0:ℝ) 1, c) = c := by
    intro c; simp
  have hbound : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, |h x| ≤ M h :=
    fun h x => (hM h).2 ⟨x, rfl⟩
  -- variance is minimized at the mean
  have hL1 : ∀ (h : C(Icc (0 : ℝ) 1, ℝ)) (c : ℝ),
      (∫ x, (h x - (∫ y, h y)) ^ 2) ≤ (∫ x, (h x - c) ^ 2) := by
    intro h c
    have hhc : Continuous (fun x => h x) := h.continuous
    have i1 : MeasureTheory.Integrable (fun x => h x) MeasureTheory.volume := hI _ hhc
    have i2 : MeasureTheory.Integrable (fun x => (h x - (∫ y, h y)) ^ 2) MeasureTheory.volume :=
      hI _ (by fun_prop)
    have i3 : MeasureTheory.Integrable (fun x => h x - (∫ y, h y)) MeasureTheory.volume :=
      hI _ (by fun_prop)
    have key2 : (∫ x, (h x - c) ^ 2) = (∫ x, ((h x - (∫ y, h y)) ^ 2
        + ((2 * ((∫ y, h y) - c)) * (h x - (∫ y, h y)) + ((∫ y, h y) - c) ^ 2))) := by
      congr 1; funext x; ring
    have key3 : (∫ x, ((h x - (∫ y, h y)) ^ 2
        + ((2 * ((∫ y, h y) - c)) * (h x - (∫ y, h y)) + ((∫ y, h y) - c) ^ 2)))
        = (∫ x, (h x - (∫ y, h y)) ^ 2)
          + ∫ x, ((2 * ((∫ y, h y) - c)) * (h x - (∫ y, h y)) + ((∫ y, h y) - c) ^ 2) :=
      MeasureTheory.integral_add i2 ((i3.const_mul _).add (MeasureTheory.integrable_const _))
    have key4 : (∫ x, ((2 * ((∫ y, h y) - c)) * (h x - (∫ y, h y)) + ((∫ y, h y) - c) ^ 2))
        = (∫ x, (2 * ((∫ y, h y) - c)) * (h x - (∫ y, h y)))
          + ∫ _x : Icc (0:ℝ) 1, ((∫ y, h y) - c) ^ 2 :=
      MeasureTheory.integral_add (i3.const_mul _) (MeasureTheory.integrable_const _)
    have e2 : (∫ x, (2 * ((∫ y, h y) - c)) * (h x - (∫ y, h y))) = 0 := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub i1
        (MeasureTheory.integrable_const _), hconst]
      simp
    rw [key2, key3, key4, e2, hconst]
    nlinarith [sq_nonneg ((∫ y, h y) - c)]
  -- |∫ f| ≤ M f
  have hμabs : ∀ h : C(Icc (0 : ℝ) 1, ℝ), (μ h) ^ 2 ≤ (M h) ^ 2 := by
    intro h
    have h1 : (∫ x, h x) ≤ M h := by
      have := MeasureTheory.integral_mono (hI _ h.continuous)
        (MeasureTheory.integrable_const (M h))
        (fun x => (le_abs_self _).trans (hbound h x))
      rwa [hconst] at this
    have h2 : -M h ≤ (∫ x, h x) := by
      have := MeasureTheory.integral_mono (hI _ (by fun_prop : Continuous fun x => -h x))
        (MeasureTheory.integrable_const (M h))
        (fun x => (neg_le_abs _).trans (hbound h x))
      rw [MeasureTheory.integral_neg, hconst] at this
      linarith
    rw [hμ h]
    exact sq_le_sq' h2 h1
  have hVarnn : ∀ h : C(Icc (0 : ℝ) 1, ℝ), 0 ≤ Var h := by
    intro h
    rw [hVar h]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  -- main chain
  have A := hL1 (f * g) (μ f * μ g)
  rw [← hμ (f * g)] at A
  rw [hVar (f * g)]
  refine A.trans ?_
  have B : (∫ x, ((f * g) x - μ f * μ g) ^ 2)
      ≤ (∫ x, (2 * ((f x - μ f) ^ 2 * (g x) ^ 2) + 2 * (μ f ^ 2) * (g x - μ g) ^ 2)) := by
    apply MeasureTheory.integral_mono
    · exact hI _ (by fun_prop)
    · exact hI _ (by fun_prop)
    · intro x
      simp only [ContinuousMap.mul_apply]
      nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
  refine B.trans ?_
  have i4 : MeasureTheory.Integrable (fun x => (f x - μ f) ^ 2 * (g x) ^ 2) MeasureTheory.volume :=
    hI _ (by fun_prop)
  have i5 : MeasureTheory.Integrable (fun x => (g x - μ g) ^ 2) MeasureTheory.volume :=
    hI _ (by fun_prop)
  have i6 : MeasureTheory.Integrable (fun x => (f x - μ f) ^ 2) MeasureTheory.volume :=
    hI _ (by fun_prop)
  rw [MeasureTheory.integral_add (i4.const_mul _) ((i5.const_mul _)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have C1 : (∫ x, (f x - μ f) ^ 2 * (g x) ^ 2) ≤ (∫ x, M g ^ 2 * (f x - μ f) ^ 2) := by
    apply MeasureTheory.integral_mono i4
    · exact (i6.const_mul _)
    · intro x
      have hg : (g x) ^ 2 ≤ M g ^ 2 :=
        sq_le_sq' (abs_le.mp (hbound g x)).1 (abs_le.mp (hbound g x)).2
      nlinarith [sq_nonneg (f x - μ f)]
  rw [MeasureTheory.integral_const_mul] at C1
  have C2 : μ f ^ 2 * (∫ x, (g x - μ g) ^ 2) ≤ M f ^ 2 * (∫ x, (g x - μ g) ^ 2) := by
    apply mul_le_mul_of_nonneg_right (hμabs f)
    rw [← hVar g]; exact hVarnn g
  have C3 : (∫ x, (f x - μ f) ^ 2) = Var f := (hVar f).symm
  have C4 : (∫ x, (g x - μ g) ^ 2) = Var g := (hVar g).symm
  rw [C3] at C1
  rw [C4] at C2
  rw [C4]
  have D1 : 2 * (∫ x, (f x - μ f) ^ 2 * g x ^ 2) ≤ 2 * (M g ^ 2 * Var f) := by linarith
  have D2 : 2 * μ f ^ 2 * Var g ≤ 2 * (M f ^ 2 * Var g) := by linarith
  linarith [D1, D2]
