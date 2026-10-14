import Mathlib

/--
Let \( D \) be a unique factorization domain.
Prove that if every nonzero prime ideal of \( D \) is maximal, then \( D \) is a principal ideal domain.
-/
theorem isPrincipalIdealRing_of_isPrime_ne_bot_isMaximal {D : Type} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] (h : ∀ P : Ideal D, [P.IsPrime] → P ≠ ⊥ → P.IsMaximal) : IsPrincipalIdealRing D := by
  refine IsPrincipalIdealRing.of_prime_ne_bot fun P hP hne => ?_
  obtain ⟨x, hx, hpx⟩ := hP.exists_mem_prime_of_ne_bot hne
  have hp : (Ideal.span {x}).IsPrime := (Ideal.span_singleton_prime hpx.ne_zero).2 hpx
  have hm : (Ideal.span {x}).IsMaximal := h _ (by
    simpa using hpx.ne_zero)
  have hle : Ideal.span {x} ≤ P := by
    rw [Ideal.span_le]; simpa using hx
  have : Ideal.span {x} = P := hm.eq_of_le hP.ne_top hle
  exact ⟨⟨x, this.symm⟩⟩
