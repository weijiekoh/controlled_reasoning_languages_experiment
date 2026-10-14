import Mathlib

/--
Let \( R \) be a Dedekind domain. Show the following:

If \( P_1, \dots, P_n \in \operatorname{Spec}(R) \) are pairwise distinct, non-zero prime ideals
and \( e_1, \dots, e_n \) are non-negative integers, there exists \( a \in R \setminus \{0\} \)
such that
\[
(a) = P_1^{e_1} \cdots P_n^{e_n} \cdot J,
\]
with \( J \subseteq R \) an ideal in whose factorization none of the \( P_i \) appear.
-/
theorem exists_factor_principal_ideal (R : Type) [CommRing R] [IsDedekindDomain R]
    (n : ℕ) (p : (Fin n) → PrimeSpectrum R) (h_nonzero : ∀ i, (p i).asIdeal ≠ ⊥)
    (h_inj : Function.Injective p) (e : (Fin n) → ℕ) :
    ∃ (a : R) (J : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * ∏ (i : Fin n), (p i).1 ^ (e i) ∧
    (∀ (i : Fin n), ¬ ∃ (K : Ideal R), J = K * (p i).1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, ⊤, one_ne_zero, by simp, fun i => i.elim0⟩
  have hmax : ∀ i, (p i).1.IsMaximal := fun i => Ideal.IsPrime.isMaximal (p i).2 (h_nonzero i)
  have hstrict : ∀ i, ∃ x, x ∈ (p i).1 ^ (e i) ∧ x ∉ (p i).1 ^ (e i + 1) := by
    intro i
    haveI := (p i).2
    obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (h_nonzero i) (e i))
    exact ⟨x, hx, hx2⟩
  choose x hx1 hx2 using hstrict
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := (Finset.univ : Finset (Fin n)))
    (fun i => (p i).1) (fun i => e i + 1)
    (fun i _ => (Ideal.prime_of_isPrime (h_nonzero i) (p i).2))
    (fun i _ j _ hij h => hij (h_inj (PrimeSpectrum.ext h))) (fun i => x i.1)
  have hy1 : ∀ i, y ∉ (p i).1 ^ (e i + 1) := by
    intro i hyi
    apply hx2 i
    have := Ideal.sub_mem _ hyi (hy i (Finset.mem_univ i))
    simpa using this
  have hy2 : ∀ i, y ∈ (p i).1 ^ (e i) := by
    intro i
    have h1 := hy i (Finset.mem_univ i)
    have h2 : y - x i ∈ (p i).1 ^ (e i) := Ideal.pow_le_pow_right (by omega) h1
    simpa using Ideal.add_mem _ h2 (hx1 i)
  have hcop : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun IsCoprime (fun i => (p i).1 ^ (e i))) := by
    intro i _ j _ hij
    apply IsCoprime.pow
    rw [Ideal.isCoprime_iff_sup_eq]
    apply (hmax i).coprime_of_ne (hmax j)
    intro h; exact hij (h_inj (PrimeSpectrum.ext h))
  have hI : y ∈ ∏ i, (p i).1 ^ (e i) := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]
    simp only [Submodule.mem_iInf]
    intro i _; exact hy2 i
  have hdvd : ∏ i, (p i).1 ^ (e i) ∣ Ideal.span {y} := by
    rw [Ideal.dvd_iff_le, Ideal.span_le]; simpa using hI
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨y, J, ?_, by rw [hJ, mul_comm], ?_⟩
  · intro h; apply hy1 ⟨0, by omega⟩; rw [h]; exact zero_mem _
  rintro i ⟨K, hK⟩
  apply hy1 i
  have hle : ∏ j, (p j).1 ^ (e j) ≤ (p i).1 ^ (e i) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (p i).1 ^ (e i)) (Finset.mem_univ i)]
    exact Ideal.mul_le_left
  have : Ideal.span {y} ≤ (p i).1 ^ (e i + 1) := by
    rw [hJ, hK, pow_succ]
    exact Ideal.mul_mono hle Ideal.mul_le_right
  exact this (Ideal.mem_span_singleton_self y)
