import Mathlib

open Ideal
/--
Let $A$ be a Noetherian ring and let $x \in A$ be an element which is
neither a unit nor a zero-divisor. Prove that the ideals $xA$ and $x^nA$
for $n = 1, 2, \dots$ have the same prime divisors:
\[
\operatorname{Ass}_A(A/xA) = \operatorname{Ass}_A(A/x^nA).
\]
-/
  have hcan : ∀ a b : A, x * a = x * b → a = b := by
    intro a b hab
    have h1 : (a - b) * x = 0 := by
      rw [sub_mul, mul_comm a, mul_comm b, hab, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hx) _ h1)
  have hcanp : ∀ (k : ℕ) (a b : A), x ^ k * a = x ^ k * b → a = b := by
    intro k
    induction k with
    | zero => intro a b h; simpa using h
    | succ k ih =>
      intro a b h
      apply ih
      apply hcan
      rw [← mul_assoc, ← mul_assoc, ← pow_succ']
      exact h
  have hspan : ∀ (m : ℕ) (r : A), r ∈ span {x ^ m} ↔ ∃ s, r = x ^ m * s := by
    intro m r
    rw [mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
  have hmem : ∀ (m : ℕ) (r c : A), r ∈ (⊥ : Submodule A (A ⧸ span {x ^ m})).colon {Submodule.Quotient.mk c} ↔ r * c ∈ span {x ^ m} := by
    intro m r c
    rw [Submodule.mem_colon_singleton]
    rw [← Submodule.Quotient.mk_smul, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    rfl
  have hmem1 : ∀ (r c : A), r ∈ (⊥ : Submodule A (A ⧸ span {x})).colon {Submodule.Quotient.mk c} ↔ r * c ∈ span {x} := by
    intro r c
    have := hmem 1 r c
    simpa using this
  have key : ∀ m : ℕ, 1 ≤ m → ∀ P : Ideal A, P.IsPrime → ∀ c : A,
      (∀ r, r ∈ P ↔ r * c ∈ span {x ^ m}) → c ∉ span {x ^ m} →
      ∃ d : A, ∀ r, r ∈ P ↔ r * d ∈ span {x ^ 1} := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro P _ c hc _; exact ⟨c, hc⟩
    | succ m hm ih =>
      intro P hP c hc hnc
      by_cases hcx : c ∈ span {x ^ 1}
      · obtain ⟨c', hc'⟩ := (hspan 1 c).mp hcx
        apply ih P hP c'
        · intro r
          rw [hc r, hspan, hspan]
          constructor
          · rintro ⟨s, hs⟩
            refine ⟨s, hcanp 1 _ _ ?_⟩
            rw [hc'] at hs
            calc x ^ 1 * (r * c') = r * (x ^ 1 * c') := by ring
              _ = x ^ (m+1) * s := hs
              _ = _ := by ring
          · rintro ⟨s, hs⟩
            refine ⟨s, ?_⟩
            rw [hc']
            calc r * (x ^ 1 * c') = x ^ 1 * (r * c') := by ring
              _ = x ^ 1 * (x ^ m * s) := by rw [hs]
              _ = _ := by ring
        · intro hh
          apply hnc
          obtain ⟨s, hs⟩ := (hspan m _).mp hh
          rw [hspan]
          refine ⟨s, ?_⟩
          rw [hc']
          calc x ^ 1 * c' = x ^ 1 * (x^m * s) := by rw [hs]
            _ = _ := by ring
      · exfalso
        have h1 : x ^ (m+1) ∈ P := by
          rw [hc]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
        have h2 : x ∈ P := hP.mem_of_pow_mem _ h1
        have h3 := (hc x).mp h2
        obtain ⟨s, hs⟩ := (hspan _ _).mp h3
        have : c = x ^ m * s := hcan _ _ (by
          calc x * c = x ^ (m+1) * s := hs
            _ = _ := by ring)
        apply hcx
        rw [hspan]
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact ⟨x ^ m' * s, by rw [this]; ring⟩
  ext P
  constructor
  · intro hP
    rw [isAssociatedPrime_iff] at hP ⊢
    obtain ⟨hPp, y, hy⟩ := hP
    refine ⟨hPp, ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨Submodule.Quotient.mk (x ^ (n-1) * a), ?_⟩
    rw [hy]
    ext r
    rw [hmem1, hmem]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [← pow_one x, hspan, hspan]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      calc r * (x ^ n' * a) = x ^ n' * (r * a) := by ring
        _ = x ^ n' * (x ^ 1 * s) := by rw [hs]
        _ = _ := by ring
    · rintro ⟨s, hs⟩
      refine ⟨s, hcanp n' _ _ ?_⟩
      calc x ^ n' * (r * a) = r * (x ^ n' * a) := by ring
        _ = x ^ (n'+1) * s := hs
        _ = _ := by ring
  · intro hP
    rw [isAssociatedPrime_iff] at hP ⊢
    obtain ⟨hPp, y, hy⟩ := hP
    refine ⟨hPp, ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' : ∀ r, r ∈ P ↔ r * a ∈ span {x ^ n} := fun r => by rw [hy, hmem]
    by_cases ha : a ∈ span {x ^ n}
    · exfalso
      have : (1 : A) ∈ P := (hy' 1).mpr (by simpa using ha)
      exact hPp.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    obtain ⟨d, hd⟩ := key n h P hPp a hy' ha
    refine ⟨Submodule.Quotient.mk d, ?_⟩
    ext r
    rw [hd r, hmem1]
    simp
