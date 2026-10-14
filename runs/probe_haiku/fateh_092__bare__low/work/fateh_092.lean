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
  classical
  have hTop : ∀ i, (p i).1 ≠ ⊤ := fun i => (p i).2.ne_top
  have hmax : ∀ i, (p i).1.IsMaximal := fun i => Ideal.IsPrime.isMaximal (p i).2 (h_nonzero i)
  have hne : ∀ i j, i ≠ j → (p i).1 ≠ (p j).1 := by
    intro i j hij h
    exact hij (h_inj (PrimeSpectrum.ext h))
  have hcopP : ∀ i j, i ≠ j → IsCoprime (p i).1 (p j).1 := fun i j hij =>
    Ideal.isCoprime_iff_sup_eq.mpr ((hmax i).coprime_of_ne (hmax j) (hne i j hij))
  have hcopF : ∀ f : Fin n → ℕ, Pairwise (Function.onFun IsCoprime fun i => (p i).1 ^ (f i)) := by
    intro f i j hij
    exact (hcopP i j hij).pow
  have key : ∃ a : R, a ≠ 0 ∧ (∀ i, a ∈ (p i).1 ^ (e i)) ∧ (∀ i, a ∉ (p i).1 ^ (e i + 1)) := by
    rcases isEmpty_or_nonempty (Fin n) with hE | hNE
    · exact ⟨1, one_ne_zero, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
    · obtain ⟨u, hu1, hu2⟩ : ∃ u : Fin n → R, (∀ i, u i ∈ (p i).1 ^ (e i)) ∧ (∀ i, u i ∉ (p i).1 ^ (e i + 1)) := by
        choose u hu1 hu2 using fun i => Ideal.exists_mem_pow_notMem_pow_succ (p i).1 (h_nonzero i) (hTop i) (e i)
        exact ⟨u, hu1, hu2⟩
      obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal (hcopF (fun i => e i + 1)) u
      have hA : ∀ i, a ∈ (p i).1 ^ (e i) := by
        intro i
        have h1 : a - u i ∈ (p i).1 ^ (e i) := Ideal.pow_le_pow_right (Nat.le_succ _) (ha i)
        have := Ideal.add_mem _ h1 (hu1 i)
        simpa using this
      have hNA : ∀ i, a ∉ (p i).1 ^ (e i + 1) := by
        intro i hi
        apply hu2 i
        have := Ideal.sub_mem _ hi (ha i)
        simpa using this
      refine ⟨a, ?_, hA, hNA⟩
      rintro rfl
      exact hNA hNE.some (Ideal.zero_mem _)
  obtain ⟨a, hane, hA, hNA⟩ := key
  have hpw : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun IsCoprime fun i => (p i).1 ^ (e i)) := fun i _ j _ hij => hcopF e hij
  have hI : Ideal.span {a} ≤ ∏ i, (p i).1 ^ (e i) := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hpw]
    refine le_iInf₂ fun i _ => ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact hA i
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).mpr hI
  refine ⟨a, J, hane, ?_, ?_⟩
  · rw [hJ, mul_comm]
  · rintro i ⟨K, hK⟩
    apply hNA i
    rw [← Ideal.span_singleton_le_iff_mem, hJ, hK, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hc : ∀ R' : Ideal R, (((p i).1 ^ (e i)) * R') * (K * (p i).1) = ((p i).1 ^ (e i) * (p i).1) * (R' * K) := by
      intro R'; ring
    rw [hc, ← pow_succ]
    exact Ideal.mul_le_left
