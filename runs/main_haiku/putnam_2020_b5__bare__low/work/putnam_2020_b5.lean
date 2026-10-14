import Mathlib

open Filter Topology Set

/--
For $j \in \{1, 2, 3, 4\}$, let $z_j$ be a complex number with $|z_j| = 1$ and $z_j \neq 1$. Prove that \[ 3 - z_1 - z_2 - z_3 - z_4 + z_1 z_2 z_3 z_4 \neq 0. \]
-/
theorem putnam_2020_b5
(z : Fin 4 → ℂ)
(hzle1 : ∀ n, ‖z n‖ = 1)
(hzne1 : ∀ n, z n ≠ 1)
: 3 - z 0 - z 1 - z 2 - z 3 + (z 0) * (z 1) * (z 2) * (z 3) ≠ 0:= by
  intro H
  have hre : ∀ n, (1 - z n)⁻¹.re = 1/2 := by
    intro n
    have h1 := hzle1 n
    have hn : z n = ⟨(z n).re, (z n).im⟩ := rfl
    have hsq : (z n).re ^ 2 + (z n).im ^ 2 = 1 := by
      have := Complex.sq_norm (z n)
      rw [h1, Complex.normSq_apply] at this
      nlinarith [this]
    have ha : (z n).re ≠ 1 := by
      intro ha
      apply hzne1 n
      apply Complex.ext
      · simpa using ha
      · have : (z n).im ^ 2 = 0 := by nlinarith
        simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hne : (1 - (z n).re) ^ 2 + (z n).im ^ 2 ≠ 0 := by
      intro h0; apply ha; nlinarith
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    have : (1 - (z n).re) * (1 - (z n).re) + (0 - (z n).im) * (0 - (z n).im) ≠ 0 := by
      convert hne using 1; ring
    rw [div_eq_iff this]
    nlinarith [hsq]
  have hw : ∀ n, (1 - z n) ≠ 0 := fun n h => hzne1 n (by linear_combination -h)
  have hz : ∀ n, z n = 1 - ((1 - z n)⁻¹)⁻¹ := by intro n; simp
  set w : Fin 4 → ℂ := fun n => (1 - z n)⁻¹ with hwdef
  have hre' : ∀ n, (w n).re = 1/2 := hre
  have hwne : ∀ n, w n ≠ 0 := fun n => inv_ne_zero (hw n)
  have hwz : ∀ n, z n = 1 - (w n)⁻¹ := hz
  rw [hwz 0, hwz 1, hwz 2, hwz 3] at H
  have G : (w 0*w 1+w 0*w 2+w 0*w 3+w 1*w 2+w 1*w 3+w 2*w 3) - (w 0+w 1+w 2+w 3) + 1 = 0 := by
    have h0 := hwne 0; have h1 := hwne 1; have h2 := hwne 2; have h3 := hwne 3
    field_simp at H
    linear_combination H
  have hform : ∀ n, w n = 1/2 + ((w n).im : ℂ) * Complex.I := by
    intro n
    apply Complex.ext <;> simp [hre' n]
  rw [hform 0, hform 1, hform 2, hform 3] at G
  have hG1 := congrArg Complex.re G
  have hG2 := congrArg Complex.im G
  simp at hG1 hG2
  have hS : (w 0).im + (w 1).im + (w 2).im + (w 3).im = 0 := by linarith
  have hS2 : ((w 0).im + (w 1).im + (w 2).im + (w 3).im)^2 = 0 := by rw [hS]; ring
  nlinarith [hG1, hS2, sq_nonneg (w 0).im, sq_nonneg (w 1).im, sq_nonneg (w 2).im, sq_nonneg (w 3).im]
