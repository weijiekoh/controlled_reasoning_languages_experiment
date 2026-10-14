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
  have key : ∀ n, (1 - z n)⁻¹.re = 1/2 := by
    intro n
    have hn : (z n).re * (z n).re + (z n).im * (z n).im = 1 := by
      have h := Complex.sq_norm (z n)
      rw [hzle1 n, Complex.normSq_apply] at h
      linarith
    have hx : (z n).re ≠ 1 := by
      intro hx
      apply hzne1 n
      apply Complex.ext
      · simpa using hx
      · have : (z n).im * (z n).im = 0 := by rw [hx] at hn; linarith
        simpa using this
    have hle : (z n).re ≤ 1 := by nlinarith [sq_nonneg (z n).im, sq_nonneg ((z n).re - 1)]
    have hd : (1 - (z n).re) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hpos : 0 < 1 - (z n).re := lt_of_le_of_ne (by linarith) (Ne.symm hd)
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    rw [div_eq_iff]
    · nlinarith
    · exact ne_of_gt (by nlinarith [mul_pos hpos hpos, mul_self_nonneg (z n).im])
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → ℂ, ∀ n, w n = (1 - z n)⁻¹ := ⟨_, fun n => rfl⟩
  have hz : ∀ n, z n = 1 - (w n)⁻¹ := by
    intro n; rw [hw, inv_inv]; ring
  have hwre : ∀ n, (w n).re = 1/2 := by
    intro n; rw [hw]; exact key n
  have hw0 : ∀ n, w n ≠ 0 := by
    intro n; rw [hw]; exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm (hzne1 n)))
  intro h
  have h' := h
  rw [hz 0, hz 1, hz 2, hz 3] at h'
  have iden2 : (w 0 * w 1 + w 0 * w 2 + w 0 * w 3 + w 1 * w 2 + w 1 * w 3 + w 2 * w 3)
      - (w 0 + w 1 + w 2 + w 3) + 1
      = (3 - (1 - (w 0)⁻¹) - (1 - (w 1)⁻¹) - (1 - (w 2)⁻¹) - (1 - (w 3)⁻¹)
          + (1 - (w 0)⁻¹) * (1 - (w 1)⁻¹) * (1 - (w 2)⁻¹) * (1 - (w 3)⁻¹))
        * (w 0 * w 1 * w 2 * w 3) := by
    have := hw0 0; have := hw0 1; have := hw0 2; have := hw0 3
    field_simp
    ring
  rw [h'] at iden2
  rw [zero_mul] at iden2
  have hr := congrArg Complex.re iden2
  have hi := congrArg Complex.im iden2
  simp [Complex.mul_re, Complex.mul_im, hwre] at hr hi
  have hY : (w 0).im + (w 1).im + (w 2).im + (w 3).im = 0 := by linarith
  have hY2 : ((w 0).im + (w 1).im + (w 2).im + (w 3).im)^2 = 0 := by rw [hY]; ring
  nlinarith [sq_nonneg (w 0).im, sq_nonneg (w 1).im, sq_nonneg (w 2).im, sq_nonneg (w 3).im]
