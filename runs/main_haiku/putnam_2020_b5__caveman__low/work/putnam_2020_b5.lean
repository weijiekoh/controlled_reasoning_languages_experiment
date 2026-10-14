import Mathlib

open Filter Topology Set

/--
For $j \in \{1, 2, 3, 4\}$, let $z_j$ be a complex number with $|z_j| = 1$ and $z_j \neq 1$. Prove that \[ 3 - z_1 - z_2 - z_3 - z_4 + z_1 z_2 z_3 z_4 \neq 0. \]
-/
theorem putnam_2020_b5
(z : Fin 4 → ℂ)
(hzle1 : ∀ n, ‖z n‖ = 1)
(hzne1 : ∀ n, z n ≠ 1)
: 3 - z 0 - z 1 - z 2 - z 3 + (z 0) * (z 1) * (z 2) * (z 3) ≠ 0:=
by
  have key : ∀ w : ℂ, ‖w‖ = 1 → w ≠ 1 → ((1 - w)⁻¹).re = 1/2 := by
    intro w hw hne
    have hn : Complex.normSq w = 1 := by
      rw [Complex.normSq_eq_norm_sq, hw]; norm_num
    rw [Complex.normSq_apply] at hn
    have hx : w.re ≠ 1 := by
      intro hx
      apply hne
      have him : w.im = 0 := by
        rw [hx] at hn
        have : w.im * w.im = 0 := by linarith
        exact mul_self_eq_zero.mp this
      apply Complex.ext <;> simp [hx, him]
    have hd : (1 - w.re) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [div_eq_iff]
    · nlinarith
    · intro h0
      apply hd
      nlinarith [mul_self_nonneg (w.im)]
  have iden : ∀ z0 z1 z2 z3 p0 p1 p2 p3 : ℂ, z0 = 1 - p0 → z1 = 1 - p1 → z2 = 1 - p2 → z3 = 1 - p3 →
      p0 ≠ 0 → p1 ≠ 0 → p2 ≠ 0 → p3 ≠ 0 →
      3 - z0 - z1 - z2 - z3 + z0*z1*z2*z3 = p0*p1*p2*p3 *
        ((p0⁻¹*p1⁻¹ + p0⁻¹*p2⁻¹ + p0⁻¹*p3⁻¹ + p1⁻¹*p2⁻¹ + p1⁻¹*p3⁻¹ + p2⁻¹*p3⁻¹)
          - (p0⁻¹ + p1⁻¹ + p2⁻¹ + p3⁻¹) + 1) := by
    intro z0 z1 z2 z3 p0 p1 p2 p3 e0 e1 e2 e3 h0 h1 h2 h3
    subst e0 e1 e2 e3
    field_simp
    ring
  have gen : ∀ a0 a1 a2 a3 : ℂ, a0.re = 1/2 → a1.re = 1/2 → a2.re = 1/2 → a3.re = 1/2 →
      a0*a1 + a0*a2 + a0*a3 + a1*a2 + a1*a3 + a2*a3 - (a0+a1+a2+a3) + 1 ≠ 0 := by
    intro a0 a1 a2 a3 ha0 ha1 ha2 ha3 hF
    have hre := congrArg Complex.re hF
    have him := congrArg Complex.im hF
    simp [ha0, ha1, ha2, ha3] at hre him
    nlinarith [sq_nonneg a0.im, sq_nonneg a1.im, sq_nonneg a2.im, sq_nonneg a3.im,
      sq_nonneg (a0.im + a1.im + a2.im + a3.im)]
  intro h
  have hp : ∀ n, 1 - z n ≠ 0 := fun n h' => hzne1 n (by linear_combination -h')
  have hI := iden (z 0) (z 1) (z 2) (z 3) (1 - z 0) (1 - z 1) (1 - z 2) (1 - z 3)
    (by ring) (by ring) (by ring) (by ring) (hp 0) (hp 1) (hp 2) (hp 3)
  rw [hI] at h
  have hF := (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (hp 0) (hp 1)) (hp 2)) (hp 3))
  exact gen _ _ _ _ (key _ (hzle1 0) (hzne1 0)) (key _ (hzle1 1) (hzne1 1))
    (key _ (hzle1 2) (hzne1 2)) (key _ (hzle1 3) (hzne1 3))
    hF
