import Mathlib
open Finset

lemma horner (a : ℕ → ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1) (z : ℂ) (hz : 3/2 ≤ z.re) (n : ℕ)
    (hn : a n = 1) : ∀ m ≤ n, 3/2 ≤ ‖(∑ i ∈ range (m+1), a (n-m+i) * z^i) + 1/2‖ := by
  have hzn : 3/2 ≤ ‖z‖ := le_trans hz (Complex.re_le_norm z)
  have h1 : ‖1 - z‖ ≤ ‖z‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  have h3 : ‖3 - z‖ ≤ ‖z‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  intro m
  induction m with
  | zero => intro _; simp [hn]; norm_num
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    have e : (∑ i ∈ range (m+1+1), a (n-(m+1)+i) * z^i) + 1/2
        = z * ((∑ i ∈ range (m+1), a (n-m+i) * z^i) + 1/2) + (a (n-(m+1)) + (1 - z)/2) := by
      rw [sum_range_succ' _ (m+1)]
      have : ∀ i ∈ range (m+1), a (n-(m+1)+(i+1)) * z^(i+1) = z * (a (n-m+i) * z^i) := by
        intro i _
        have : n-(m+1)+(i+1) = n-m+i := by omega
        rw [this]; ring
      rw [sum_congr rfl this, ← mul_sum]
      simp; ring
    rw [e]
    have hc : ‖a (n-(m+1)) + (1 - z)/2‖ ≤ ‖z‖/2 := by
      rcases ha (n-(m+1)) with h | h <;> rw [h]
      · simp; linarith
      · have : (1:ℂ) + (1 - z)/2 = (3 - z)/2 := by ring
        rw [this, norm_div]; simp; linarith
    have := norm_sub_norm_le (z * ((∑ i ∈ range (m+1), a (n-m+i) * z^i) + 1/2)) (-(a (n-(m+1)) + (1 - z)/2))
    rw [sub_neg_eq_add, norm_neg, norm_mul] at this
    nlinarith [norm_nonneg ((∑ i ∈ range (m+1), a (n-m+i) * z^i) + 1/2)]

lemma rootre (P : Polynomial ℤ) (hP : P ≠ 0) (h : ∀ n, P.coeff n = 0 ∨ P.coeff n = 1)
    (z : ℂ) (hz : Polynomial.aeval z P = 0) : z.re < 3/2 := by
  by_contra hc
  push_neg at hc
  have hl : P.coeff P.natDegree = 1 := by
    rcases h P.natDegree with h | h
    · exact absurd (by simpa using h) (by simpa [Polynomial.leadingCoeff] using hP)
    · exact h
  have := horner (fun i => (P.coeff i : ℂ)) (by intro i; rcases h i with h | h <;> simp [h]) z hc
    P.natDegree (by simp [hl]) P.natDegree le_rfl
  rw [Polynomial.aeval_eq_sum_range] at hz
  simp only [Nat.sub_self, zero_add, smul_eq_mul] at this hz
  simp at hz
  rw [show (∑ i ∈ range (P.natDegree+1), (P.coeff i : ℂ) * z^i) = 0 from by simpa using hz] at this
  norm_num at this
