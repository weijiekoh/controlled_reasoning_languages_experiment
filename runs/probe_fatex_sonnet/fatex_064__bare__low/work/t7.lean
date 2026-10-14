import Mathlib
open MvPolynomial

abbrev S0 (k : Type) [Field k] : Set (MvPolynomial (Fin 2) k) := {(X 0) ^ 4, (X 0) ^ 3 * X 1,
      X 0 * (X 1) ^ 3, (X 1) ^ 4}

theorem Qmem (k : Type) [Field k] (y : MvPolynomial (Fin 2) k) (hy : y ∈ Algebra.adjoin k (S0 k)) :
    ((X 0 : MvPolynomial (Fin 2) k) ^ 2 * X 1 ^ 2) * (y - C (constantCoeff y)) ∈ Algebra.adjoin k (S0 k) := by
  have g1 : (X 0 ^ 4 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  have g2 : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  have g3 : (X 0 * X 1 ^ 3 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  have g4 : (X 1 ^ 4 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    simp only [S0, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · have := mul_mem g2 g2
      convert this using 1
      simp; ring
    · have := mul_mem g1 g3
      convert this using 1
      simp; ring
    · have := mul_mem g2 g4
      convert this using 1
      simp; ring
    · have := mul_mem g3 g3
      convert this using 1
      simp; ring
  | algebraMap c =>
    simp [MvPolynomial.algebraMap_eq]
  | add y z hy hz ihy ihz =>
    have := add_mem ihy ihz
    convert this using 1
    simp only [map_add, C_add]; ring
  | mul y z hy hz ihy ihz =>
    have := add_mem (mul_mem ihy hz) (mul_mem (Subalgebra.algebraMap_mem _ (constantCoeff y)) ihz)
    convert this using 1
    simp only [map_mul, C_mul, MvPolynomial.algebraMap_eq]; ring

theorem Qsupp (k : Type) [Field k] (y : MvPolynomial (Fin 2) k) (hy : y ∈ Algebra.adjoin k (S0 k)) :
    ∀ d, coeff d y ≠ 0 → d = 0 ∨ (4 ≤ d 0 + d 1 ∧ (d 0 + d 1) % 4 = 0 ∧
      d ≠ Finsupp.single 0 2 + Finsupp.single 1 2) := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    intro d hd
    right
    simp only [S0, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have e1 : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) k) = monomial (Finsupp.single 0 3 + Finsupp.single 1 1) 1 := by
      rw [X_pow_eq_monomial, X, monomial_mul, one_mul]
    have e2 : (X 0 * X 1 ^ 3 : MvPolynomial (Fin 2) k) = monomial (Finsupp.single 0 1 + Finsupp.single 1 3) 1 := by
      rw [X_pow_eq_monomial, X, monomial_mul, one_mul]
    rcases hy with rfl | rfl | rfl | rfl
    · rw [X_pow_eq_monomial, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
    · rw [e1, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
    · rw [e2, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
    · rw [X_pow_eq_monomial, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
  | algebraMap c =>
    intro d hd
    left
    rw [MvPolynomial.algebraMap_eq, coeff_C] at hd
    split_ifs at hd with h
    · exact h.symm
    · exact absurd rfl hd
  | add y z hy hz ihy ihz =>
    intro d hd
    rw [coeff_add] at hd
    by_cases h : coeff d y = 0
    · rw [h, zero_add] at hd; exact ihz d hd
    · exact ihy d h
  | mul y z hy hz ihy ihz =>
    intro d hd
    rw [coeff_mul] at hd
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 : coeff x.1 y ≠ 0 := left_ne_zero_of_mul hne
    have h2 : coeff x.2 z ≠ 0 := right_ne_zero_of_mul hne
    subst hx
    rcases ihy _ h1 with h | h
    · rw [h, zero_add]; exact ihz _ h2
    · rcases ihz _ h2 with h' | h'
      · rw [h', add_zero]; exact Or.inr h
      · right
        obtain ⟨a1, a2, a3⟩ := h
        obtain ⟨b1, b2, b3⟩ := h'
        simp only [Finsupp.add_apply]
        refine ⟨by omega, by omega, ?_⟩
        intro h5
        have := congrArg (fun f => f 0 + f 1) h5
        simp at this
        omega
