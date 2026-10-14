import Mathlib

open Function Set MeasureTheory

theorem putnam_2013_b4
    (μ Var M : C(Icc (0 : ℝ) 1, ℝ) → ℝ)
    (hμ : ∀ f, μ f = ∫ x, f x)
    (hVar : ∀ f, Var f = ∫ x, (f x - μ f) ^ 2)
    (hM : ∀ f : C(Icc (0 : ℝ) 1, ℝ), IsGreatest (range <| abs ∘ f) (M f))
    (f g : C(Icc (0 : ℝ) 1, ℝ)) :
    Var (f * g) ≤ 2 * Var f * (M g) ^ 2 + 2 * Var g * (M f) ^ 2 := by
  have : IsFiniteMeasure (volume : Measure (Icc (0:ℝ) 1)) := CompactSpace.isFiniteMeasure
  have hv : volume.real (univ : Set (Icc (0:ℝ) 1)) = 1 := by
    simp [Measure.real]
  have hI : ∀ F : Icc (0:ℝ) 1 → ℝ, Continuous F → Integrable F := fun F h =>
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hb : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, |h x| ≤ M h := fun h x => (hM h).2 ⟨x, rfl⟩
  have hMnn : ∀ h : C(Icc (0 : ℝ) 1, ℝ), 0 ≤ M h := fun h =>
    le_trans (abs_nonneg _) (hb h ⟨0, by simp⟩)
  have hsq : ∀ h : C(Icc (0 : ℝ) 1, ℝ), ∀ x, (h x)^2 ≤ (M h)^2 := fun h x => by
    have := hb h x
    nlinarith [sq_abs (h x), abs_nonneg (h x), hMnn h]
  have hVnn : ∀ h : C(Icc (0 : ℝ) 1, ℝ), 0 ≤ Var h := fun h => by
    rw [hVar]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hmu : ∀ h : C(Icc (0 : ℝ) 1, ℝ), (μ h)^2 ≤ (M h)^2 := fun h => by
    rw [hμ]
    have h1 : ∫ x, h x ≤ ∫ x, M h := integral_mono (hI _ h.continuous) (hI _ continuous_const)
      (fun x => (abs_le.mp (hb h x)).2)
    have h2 : ∫ x, -(M h) ≤ ∫ x, h x :=
      integral_mono (hI _ continuous_const) (hI _ h.continuous)
        (fun x => (abs_le.mp (hb h x)).1)
    simp only [integral_const, hv, smul_eq_mul] at h1 h2
    nlinarith [hMnn h]
  have key : ∀ (G : Icc (0:ℝ) 1 → ℝ) (c : ℝ), Continuous G →
      ∫ x, (G x - ∫ y, G y)^2 ≤ ∫ x, (G x - c)^2 := by
    intro G c hG
    obtain ⟨m, hm⟩ : ∃ m, m = ∫ y, G y := ⟨_, rfl⟩
    rw [← hm]
    have i1 : Integrable fun x => (G x - m)^2 := hI _ ((hG.sub continuous_const).pow 2)
    have i2 : Integrable fun x => 2 * (m - c) * (G x - m) :=
      hI _ (continuous_const.mul (hG.sub continuous_const))
    have i3 : Integrable fun _ : Icc (0:ℝ) 1 => (m - c)^2 := integrable_const _
    have hz : ∫ x, (G x - m) = 0 := by
      rw [integral_sub (hI _ hG) (hI _ continuous_const), integral_const, hv, ← hm]
      simp
    have e : ∀ x, (G x - c)^2 = (G x - m)^2 + (2*(m-c)) * (G x - m) + (m-c)^2 :=
      fun x => by ring
    have i12 : Integrable fun x => (G x - m)^2 + 2 * (m - c) * (G x - m) := i1.add i2
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add i12 i3,
      integral_add i1 i2, integral_const_mul, hz, integral_const, hv]
    simp
    positivity
  have k1 : ∫ x, ((f * g) x - μ (f * g))^2 ≤ ∫ x, ((f * g) x - μ f * μ g)^2 := by
    rw [hμ (f * g)]
    exact key (fun x => (f * g) x) _ (f * g).continuous
  have hsplit : ∀ x, ((f * g) x - μ f * μ g)^2 ≤
      2 * ((f x - μ f) * g x)^2 + 2 * (μ f * (g x - μ g))^2 := fun x => by
    have : (f * g) x - μ f * μ g = (f x - μ f) * g x + μ f * (g x - μ g) := by
      rw [ContinuousMap.mul_apply]; ring
    rw [this]
    nlinarith [sq_nonneg ((f x - μ f) * g x - μ f * (g x - μ g))]
  have hintA : Integrable fun x => ((f x - μ f) * g x)^2 :=
    hI _ ((((f.continuous.sub continuous_const)).mul g.continuous).pow 2)
  have hintB : Integrable fun x => (μ f * (g x - μ g))^2 :=
    hI _ (((continuous_const.mul (g.continuous.sub continuous_const))).pow 2)
  have hintC : Integrable fun x => ((f * g) x - μ f * μ g)^2 :=
    hI _ ((((f * g).continuous).sub continuous_const).pow 2)
  have k2 : ∫ x, ((f * g) x - μ f * μ g)^2 ≤
      ∫ x, (2 * ((f x - μ f) * g x)^2 + 2 * (μ f * (g x - μ g))^2) :=
    integral_mono hintC ((hintA.const_mul 2).add (hintB.const_mul 2)) hsplit
  have k3 : ∫ x, (2 * ((f x - μ f) * g x)^2 + 2 * (μ f * (g x - μ g))^2)
      = 2 * (∫ x, ((f x - μ f) * g x)^2) + 2 * (∫ x, (μ f * (g x - μ g))^2) := by
    rw [integral_add (hintA.const_mul 2) (hintB.const_mul 2)]
    simp only [integral_const_mul]
  have hA : ∫ x, ((f x - μ f) * g x)^2 ≤ (M g)^2 * Var f := by
    rw [hVar f, ← integral_const_mul]
    apply integral_mono hintA (((hI _ ((f.continuous.sub continuous_const).pow 2))).const_mul _)
    intro x
    show ((f x - μ f) * g x)^2 ≤ (M g)^2 * (f x - μ f)^2
    have := mul_le_mul_of_nonneg_left (hsq g x) (sq_nonneg (f x - μ f))
    nlinarith [this]
  have hB : ∫ x, (μ f * (g x - μ g))^2 ≤ (M f)^2 * Var g := by
    have e : ∀ x, (μ f * (g x - μ g))^2 = (μ f)^2 * (g x - μ g)^2 := fun x => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, hVar g]
    exact mul_le_mul_of_nonneg_right (hmu f) (by rw [← hVar g]; exact hVnn g)
  rw [hVar (f * g)]
  have hVg := hVnn g
  have hVf := hVnn f
  linarith [k1, k2, k3, hA, hB]
