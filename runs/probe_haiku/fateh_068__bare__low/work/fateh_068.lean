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
theorem associatedPrimes_quot_span_eq_quot_span_pow {A : Type} [CommRing A] [IsNoetherianRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (hx' : ¬ IsUnit x) (n : ℕ) (h : n ≥ 1) :
    associatedPrimes A (A ⧸ span {x}) = associatedPrimes A (A ⧸ span {x ^ n}) := by
  have hann : ∀ (J : Ideal A) (y a : A), a ∈ (⊥ : Submodule A (A ⧸ J)).colon {(Ideal.Quotient.mk J y)} ↔ a * y ∈ J := by
    intro J y a
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change a • (Submodule.Quotient.mk y : A ⧸ J) = 0 ↔ _
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
  have hcan : ∀ s ∈ nonZeroDivisors A, ∀ u v : A, u * s = v * s → u = v := by
    intro s hs u v huv
    have := (mem_nonZeroDivisors_iff.mp hs).2 (u - v) (by rw [sub_mul, huv, sub_self])
    exact sub_eq_zero.mp this
  have hxk : ∀ k : ℕ, x ^ k ∈ nonZeroDivisors A := fun k => pow_mem hx k
  have hx1 : ∀ k : ℕ, ∀ u : A, u * x ∈ Ideal.span {x ^ (k+1)} ↔ u ∈ Ideal.span {x ^ k} := by
    intro k u
    constructor
    · intro h
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
      rw [Ideal.mem_span_singleton']
      refine ⟨d, ?_⟩
      apply hcan x hx
      rw [← hd]; ring
    · intro h
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
      rw [Ideal.mem_span_singleton']
      exact ⟨d, by rw [← hd]; ring⟩
  have hx2 : ∀ k : ℕ, ∀ u : A, u * x ^ k ∈ Ideal.span {x ^ (k+1)} ↔ u ∈ Ideal.span {x} := by
    intro k u
    constructor
    · intro h
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
      rw [Ideal.mem_span_singleton']
      exact ⟨d, hcan (x ^ k) (hxk k) _ _ (by rw [← hd]; ring)⟩
    · intro h
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
      rw [Ideal.mem_span_singleton']
      exact ⟨a, by rw [← ha]; ring⟩
  have key : ∀ m : ℕ, ∀ (y : A) (p : Ideal A), p.IsPrime →
      (∀ a, a ∈ p ↔ a * y ∈ Ideal.span {x ^ m}) → ∃ z : A, ∀ a, a ∈ p ↔ a * z ∈ Ideal.span {x} := by
    intro m
    induction m with
    | zero =>
      intro y p hp hyp
      exfalso
      apply hp.ne_top
      rw [Ideal.eq_top_iff_one]
      exact (hyp 1).mpr (by simp)
    | succ m ih =>
      intro y p hp hyp
      by_cases h1 : ∃ r : A, r * y ∉ Ideal.span {x ^ (m+1)} ∧ r * y ∈ Ideal.span {x}
      · obtain ⟨r, hr1, hr2⟩ := h1
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr2
        have hrp : r ∉ p := fun h => hr1 ((hyp r).mp h)
        have hpc : ∀ a, a ∈ p ↔ a * c ∈ Ideal.span {x ^ m} := by
          intro a
          have e1 : a ∈ p ↔ a * r * y ∈ Ideal.span {x ^ (m+1)} := by
            constructor
            · intro ha
              have h2 := (hyp a).mp ha
              rw [show a * r * y = r * (a * y) by ring]
              exact Ideal.mul_mem_left _ r h2
            · intro h
              have h' : a * r ∈ p := (hyp (a * r)).mpr h
              rcases hp.mem_or_mem h' with h'' | h''
              · exact h''
              · exact absurd h'' hrp
          rw [e1, show a * r * y = (a * c) * x by linear_combination (-a) * hc, hx1 m (a * c)]
        obtain ⟨z, hz⟩ := ih c p hp hpc
        exact ⟨z, hz⟩
      · refine ⟨y, fun a => ?_⟩
        constructor
        · intro ha
          have h2 := (hyp a).mp ha
          exact Ideal.mem_span_singleton.mpr
            (dvd_trans (dvd_pow_self x (Nat.succ_ne_zero m)) (Ideal.mem_span_singleton.mp h2))
        · intro ha
          by_cases hm : a * y ∈ Ideal.span {x ^ (m+1)}
          · exact (hyp a).mpr hm
          · exact absurd ⟨a, hm, ha⟩ h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  ext I
  simp only [associatedPrimes, isAssociatedPrime_iff]
  constructor
  · rintro ⟨hp, w, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨hp, Ideal.Quotient.mk (Ideal.span {x ^ (m+1)}) (x ^ m * z), ?_⟩
    ext a
    rw [hann, hann, show a * (x ^ m * z) = a * z * x ^ m by ring, hx2]
  · rintro ⟨hp, w, rfl⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨z, hz⟩ := key (m+1) y _ hp (fun a => hann _ y a)
    refine ⟨hp, Ideal.Quotient.mk (Ideal.span {x}) z, ?_⟩
    ext a
    exact (hz a).trans (hann _ z a).symm
