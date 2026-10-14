import Mathlib
open Polynomial

theorem sq5 (y : ℚ) : y ^ 2 ≠ 5 := by
  intro h
  have h5 : IsSquare ((5:ℕ):ℚ) := ⟨y, by push_cast; nlinarith⟩
  have := Rat.isSquare_natCast_iff.mp h5
  obtain ⟨m, hm⟩ := this
  have : m ≤ 3 := by nlinarith
  interval_cases m <;> omega

theorem no_rat_root (x : ℚ) : x ^ 4 - x ^ 2 - 1 ≠ 0 := by
  intro h
  exact sq5 (2 * x ^ 2 - 1) (by nlinarith)

theorem quad_form (p : ℚ[X]) (hp : p.Monic) (h : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · have := hp.coeff_natDegree
    rw [h] at this; simp [coeff_X_pow, coeff_X, this]
  · have : p.coeff (n+3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this]; simp [coeff_X, coeff_X_pow]

theorem lin_form (p : ℚ[X]) (hp : p.Monic) (h : p.natDegree = 1) :
    p = X + C (p.coeff 0) := by
  ext n
  rcases n with _ | _ | n
  · simp
  · have := hp.coeff_natDegree
    rw [h] at this; simpa using this
  · have : p.coeff (n+2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this]; simp [coeff_X, coeff_C]

theorem f_irred : Irreducible (X ^ 4 - X ^ 2 - 1 : ℚ[X]) := by
  have hm : (X ^ 4 - X ^ 2 - 1 : ℚ[X]).Monic := by monicity!
  have hdeg : (X ^ 4 - X ^ 2 - 1 : ℚ[X]).natDegree = 4 := by compute_degree!
  rw [hm.irreducible_iff_natDegree]
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg natDegree h
    rw [hdeg, natDegree_one] at this
    omega
  intro p q hp hq hpq
  have hd : p.natDegree + q.natDegree = 4 := by
    rw [← natDegree_mul hp.ne_zero hq.ne_zero, hpq, hdeg]
  have lin : ∀ p q : ℚ[X], p.Monic → p.natDegree = 1 → p * q = X ^ 4 - X ^ 2 - 1 → False := by
    intro p q hp h1 h
    have hp' := lin_form p hp h1
    have := congrArg (eval (-(p.coeff 0))) h
    rw [eval_mul] at this
    have h0 : eval (-(p.coeff 0)) p = 0 := by
      conv_lhs => rw [hp']
      simp
    rw [h0] at this
    simp at this
    exact no_rat_root _ (by linarith)
  by_contra hcon
  push_neg at hcon
  have : p.natDegree = 1 ∨ p.natDegree = 2 ∨ p.natDegree = 3 := by omega
  rcases this with h1 | h2 | h3
  · exact lin p q hp h1 hpq
  · have hq2 : q.natDegree = 2 := by omega
    have e1 := quad_form p hp h2
    have e2 := quad_form q hq hq2
    set a := p.coeff 1
    set b := p.coeff 0
    set c := q.coeff 1
    set d := q.coeff 0
    rw [e1, e2] at hpq
    have key : (X ^ 2 + C a * X + C b) * (X ^ 2 + C c * X + C d) = X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X + C (b * d) := by
      simp only [C_add, C_mul]; ring
    rw [key] at hpq
    have c0 := congrArg (coeff · 0) hpq
    have c1 := congrArg (coeff · 1) hpq
    have c2 := congrArg (coeff · 2) hpq
    have c3 := congrArg (coeff · 3) hpq
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at c0 c1 c2 c3
    norm_num at c0 c1 c2 c3
    have hc : c = -a := by linarith
    rw [hc] at c1 c2
    have h3 : a * (d - b) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · rw [h] at c2
      have hd : d = -1 - b := by linarith
      rw [hd] at c0
      exact sq5 (2 * b + 1) (by nlinarith)
    · have : d = b := by linarith
      rw [this] at c0
      nlinarith [sq_nonneg b]
  · exact lin q p hq (by omega) (by rw [mul_comm]; exact hpq)
