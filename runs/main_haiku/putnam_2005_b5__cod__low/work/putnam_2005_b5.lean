import Mathlib

open Nat Set

/--
Let $P(x_1,\dots,x_n)$ denote a polynomial with real coefficients in the variables $x_1, \dots, x_n$, and suppose that
\[
\left( \frac{\partial^2}{\partial x_1^2} + \cdots + \frac{\partial^2}{\partial x_n^2}\right) P(x_1, \dots,x_n) = 0 \quad \mbox{(identically)}
\]
and that
\[
x_1^2 + \cdots + x_n^2 \mbox{ divides } P(x_1, \dots, x_n).
\]
Show that $P=0$ identically.
-/
theorem putnam_2005_b5
(n : ℕ)
(npos : n > 0)
(P : MvPolynomial (Fin n) ℝ)
(hderiv : ∑ i : Fin n, (MvPolynomial.pderiv i)^[2] P = 0)
(hsumsq : ∑ i : Fin n, (MvPolynomial.X i) ^ 2 ∣ P)
: (P = 0) :=
by
  classical
  obtain ⟨S, hS⟩ : ∃ S : MvPolynomial (Fin n) ℝ, S = ∑ i : Fin n, MvPolynomial.X i ^ 2 := ⟨_, rfl⟩
  have hSpd : ∀ i, MvPolynomial.pderiv i S = 2 * MvPolynomial.X i := by
    intro i
    rw [hS]
    simp [map_sum, Derivation.leibniz_pow, MvPolynomial.pderiv_X, Pi.single_apply]
  have hSh : S.IsHomogeneous 2 := by
    rw [hS]
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    have := (MvPolynomial.isHomogeneous_X ℝ j).pow 2
    simpa using this
  have hS0 : S ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (fun _ : Fin n => (1:ℝ))) h
    rw [hS] at this
    simp at this
    omega
  have hZ : ∀ (ψ : MvPolynomial (Fin n) ℝ) (i : Fin n), ψ.IsHomogeneous 0 →
      MvPolynomial.pderiv i ψ = 0 := by
    intro ψ i h
    ext m
    have hd : Finsupp.degree (m + Finsupp.single i 1) ≠ 0 := by
      rw [map_add Finsupp.degree]; simp
    rw [MvPolynomial.coeff_pderiv, h.coeff_eq_zero hd, zero_mul, MvPolynomial.coeff_zero]
  have hpdhc : ∀ (F : MvPolynomial (Fin n) ℝ) (i : Fin n) (d : ℕ),
      MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent (d+1) F)
        = MvPolynomial.homogeneousComponent d (MvPolynomial.pderiv i F) := by
    intro F i d
    ext m
    have hdeg : Finsupp.degree (m + Finsupp.single i 1) = Finsupp.degree m + 1 := by
      rw [map_add Finsupp.degree]; simp
    simp only [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_homogeneousComponent, hdeg,
      Nat.add_right_cancel_iff]
    split_ifs <;> simp
  have hcmul : ∀ (A : MvPolynomial (Fin n) ℝ) (a : ℕ) (Q : MvPolynomial (Fin n) ℝ) (d : ℕ),
      A.IsHomogeneous a →
      MvPolynomial.homogeneousComponent (a+d) (A*Q)
        = A * MvPolynomial.homogeneousComponent d Q := by
    intro A a Q d hA
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q]
    rw [Finset.mul_sum, map_sum]
    rw [Finset.sum_congr rfl (fun k _ => MvPolynomial.homogeneousComponent_of_mem
      (p := A * MvPolynomial.homogeneousComponent k Q)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).2
        (hA.mul (MvPolynomial.homogeneousComponent_isHomogeneous k Q))))]
    simp only [add_right_inj]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · simp at h
      rw [MvPolynomial.homogeneousComponent_eq_zero d Q (by omega), mul_zero]
  have hE : ∀ (m : ℕ) (R : MvPolynomial (Fin n) ℝ), R.IsHomogeneous m →
      ∑ i, MvPolynomial.X i * MvPolynomial.pderiv i R = MvPolynomial.C (m:ℝ) * R := by
    intro m R h
    rw [h.sum_X_mul_pderiv, nsmul_eq_mul]
    simp
  have I1 : ∀ R : MvPolynomial (Fin n) ℝ,
      ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i (S*R))
        = S * ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i R)
          + 4 * ∑ i, MvPolynomial.X i * MvPolynomial.pderiv i R
          + MvPolynomial.C (2*(n:ℝ)) * R := by
    intro R
    have key : ∀ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i (S*R))
        = S * MvPolynomial.pderiv i (MvPolynomial.pderiv i R)
          + 4 * (MvPolynomial.X i * MvPolynomial.pderiv i R) + 2 * R := by
      intro i
      have h2 : MvPolynomial.pderiv i (2 : MvPolynomial (Fin n) ℝ) = 0 := by
        rw [show (2 : MvPolynomial (Fin n) ℝ) = MvPolynomial.C 2 from by simp [map_ofNat], MvPolynomial.pderiv_C]
      simp only [MvPolynomial.pderiv_mul, hSpd, map_add, MvPolynomial.pderiv_X, h2, Pi.single_eq_same]
      ring
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, map_ofNat]
    ring
  have hG : ∀ D : ℕ, ∀ c : ℝ, 0 < c → ∀ Q : MvPolynomial (Fin n) ℝ, Q.IsHomogeneous D →
      S * ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) + MvPolynomial.C c * Q = 0 →
      Q = 0 := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
    intro c hcpos Q hQ heq
    by_cases hD : D < 2
    · have hz : ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply hZ
        have h1 := hQ.pderiv (i := i)
        rw [show D - 1 = 0 by omega] at h1
        exact h1
      rw [hz, mul_zero, zero_add] at heq
      rcases mul_eq_zero.1 heq with h | h
      · exact absurd (MvPolynomial.C_eq_zero.1 h) hcpos.ne'
      · exact h
    · 
      have hck : MvPolynomial.C c * MvPolynomial.C c⁻¹ = (1 : MvPolynomial (Fin n) ℝ) := by
        rw [← map_mul, mul_inv_cancel₀ hcpos.ne', map_one]
      have hΔhom : (∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)).IsHomogeneous (D-1-1) :=
        MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => (hQ.pderiv (i := i)).pderiv (i := i))
      obtain ⟨R, hRdef⟩ : ∃ R : MvPolynomial (Fin n) ℝ,
          R = -(MvPolynomial.C c⁻¹ * ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) :=
        ⟨_, rfl⟩
      have hR : R.IsHomogeneous (D-1-1) := by
        have e : R = MvPolynomial.C (-1:ℝ) * (MvPolynomial.C c⁻¹ * ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) := by
          rw [hRdef, map_neg, map_one, neg_one_mul]
        rw [e]
        simpa using (MvPolynomial.isHomogeneous_C (Fin n) (-1:ℝ)).mul ((MvPolynomial.isHomogeneous_C (Fin n) c⁻¹).mul hΔhom)
      have hQR : Q = S * R := by
        rw [hRdef]
        linear_combination (MvPolynomial.C c⁻¹) * heq - Q * hck
      have hΔR := I1 R
      rw [← hQR] at hΔR
      rw [hE _ R hR] at hΔR
      rw [hΔR, hQR] at heq
      have key : S * (S * ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i R)
          + (4 * MvPolynomial.C ((D-1-1 : ℕ) : ℝ) + MvPolynomial.C (2*(n:ℝ)) + MvPolynomial.C c) * R) = 0 := by
        linear_combination heq
      have key2 := (mul_eq_zero.1 key).resolve_left hS0
      have hc' : ((4 : MvPolynomial (Fin n) ℝ) * MvPolynomial.C (((D-1-1 : ℕ)) : ℝ) + MvPolynomial.C (2*(n:ℝ)) + MvPolynomial.C c)
          = MvPolynomial.C (4 * (((D-1-1 : ℕ)) : ℝ) + 2 * (n:ℝ) + c) := by
        simp [map_add, map_mul, map_ofNat]
      rw [hc'] at key2
      have hpos : (0:ℝ) < 4 * (((D-1-1 : ℕ)) : ℝ) + 2 * (n:ℝ) + c := by
        have : (0:ℝ) ≤ 4 * (((D-1-1 : ℕ)) : ℝ) + 2 * (n:ℝ) := by positivity
        linarith
      have hR0 := ih (D-1-1) (by omega) _ hpos R hR key2
      rw [hQR, hR0, mul_zero]
  obtain ⟨Q, hQ⟩ : S ∣ P := by rw [hS]; exact hsumsq
  have hΔP : ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i P) = 0 := hderiv
  have hcomp : ∀ d : ℕ, MvPolynomial.homogeneousComponent d Q = 0 := by
    intro d
    have hRh := MvPolynomial.homogeneousComponent_isHomogeneous d Q
    have hSd : S * MvPolynomial.homogeneousComponent d Q
        = MvPolynomial.homogeneousComponent (2+d) P := by
      rw [hQ, hcmul S 2 Q d hSh]
    have hΔc : ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (MvPolynomial.homogeneousComponent (2+d) P)) = 0 := by
      have h1 : ∀ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i
          (MvPolynomial.homogeneousComponent (2+d) P))
          = MvPolynomial.homogeneousComponent d (MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) := by
        intro i
        rw [show 2 + d = (d+1)+1 by omega, hpdhc P i (d+1), hpdhc (MvPolynomial.pderiv i P) i d]
      rw [Finset.sum_congr rfl (fun i _ => h1 i), ← map_sum, hΔP, map_zero]
    rw [← hSd] at hΔc
    have I := I1 (MvPolynomial.homogeneousComponent d Q)
    rw [hΔc, hE d _ hRh] at I
    have eq : S * ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent d Q))
        + MvPolynomial.C (4 * (d:ℝ) + 2 * (n:ℝ)) * MvPolynomial.homogeneousComponent d Q = 0 := by
      rw [show MvPolynomial.C (4 * (d:ℝ) + 2 * (n:ℝ)) = 4 * MvPolynomial.C (d:ℝ) + MvPolynomial.C (2*(n:ℝ)) by
        simp [map_add, map_mul, map_ofNat]]
      linear_combination -I
    exact hG d _ (by positivity) _ hRh eq
  have hQ0 : Q = 0 := by
    rw [← MvPolynomial.sum_homogeneousComponent Q]
    exact Finset.sum_eq_zero (fun d _ => hcomp d)
  rw [hQ, hQ0, mul_zero]
