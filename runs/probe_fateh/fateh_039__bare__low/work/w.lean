import Mathlib

open Polynomial
theorem X1 :
    letI : Fact (Nat.Prime 7) := by decide +revert
    ∃ ζ : (X ^ 15 - 2 : (ZMod 7)[X]).SplittingField, IsPrimitiveRoot ζ 45 ∧
    IntermediateField.adjoin (ZMod 7) {ζ} = ⊤ := by
  have h7 : ((15:ℕ) : ZMod 7) ≠ 0 := by decide
  have h2 : (2 : ZMod 7) ≠ 0 := by decide
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  set p : (ZMod 7)[X] := X ^ 15 - 2 with hp
  have hsep : p.Separable := by
    have := Polynomial.separable_X_pow_sub_C (F := ZMod 7) (2 : ZMod 7) h7 h2
    simpa [hp, map_ofNat] using this
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := p.SplittingField) hsep (SplittingField.splits p)
  have hdeg : p.natDegree = 15 := by
    rw [hp]; compute_degree!
  rw [hdeg] at hcard
  have hmem : ∀ x : p.SplittingField, x ∈ p.rootSet p.SplittingField ↔ x ^ 15 = 2 := by
    intro x
    rw [mem_rootSet]
    refine ⟨fun ⟨_, h⟩ => ?_, fun h => ⟨hsep.ne_zero, ?_⟩⟩ <;> simp_all [hp, sub_eq_zero, map_ofNat]
  have hchar : (7 : p.SplittingField) = 0 := by
    have : ((7 : ℕ) : p.SplittingField) = 0 := CharP.cast_eq_zero_iff p.SplittingField 7 7 |>.2 dvd_rfl
    simpa using this
  have hex : ∃ α ∈ p.rootSet p.SplittingField, α ^ 9 ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (p.rootSet p.SplittingField).toFinset ⊆ (X ^ 3 - C 4 : (p.SplittingField)[X]).roots.toFinset := by
      intro x hx
      have hx' := (hmem x).1 (by simpa using hx)
      have h9 := hcon x (by simpa using hx)
      have : x ^ 3 = 4 := by
        have e6 : x^6 = 2 := by
          rw [← hx']; calc x^6 = x^9 * x^6 := by rw [h9, one_mul]
            _ = x^15 := by ring
        have e : (x^3) * 2 = 1 := by rw [← e6, ← h9]; ring
        have : x^3 = x^3 * (2*4) := by
          have : (2*4 : p.SplittingField) = 1 := by linear_combination hchar
          rw [this, mul_one]
        rw [this, ← mul_assoc, e, one_mul]
      have hne : (X ^ 3 - C 4 : (p.SplittingField)[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _
      simp [hne, this, sub_eq_zero]
    have h1 := Finset.card_le_card hsub
    have h2 := (Multiset.toFinset_card_le (X ^ 3 - C 4 : (p.SplittingField)[X]).roots).trans (card_roots' _)
    have h3 : (X ^ 3 - C 4 : (p.SplittingField)[X]).natDegree = 3 := by compute_degree!
    rw [h3] at h2
    rw [Set.toFinset_card] at h1
    simp only [hcard] at h1
    omega
  obtain ⟨α, hα, hα9⟩ := hex
  have hα15 := (hmem α).1 hα
  have hα45 : α ^ 45 = 1 := by
    have : α^45 = (α^15)^3 := by ring
    rw [this, hα15]; linear_combination hchar
  have hord : orderOf α = 45 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hα45
    intro q hq hdvd
    have : q ∣ 3^2 * 5 := by norm_num; exact hdvd
    have h45 : q ∣ 3^2 * 5 := by norm_num; exact hdvd
    rcases (Nat.Prime.dvd_mul hq).1 h45 with h | h
    · have := hq.dvd_of_dvd_pow h
      have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 this
      subst this
      have e : (45 / 3 : ℕ) = 15 := by norm_num
      rw [e, hα15]
      intro h; have : (1:p.SplittingField) = 0 := by linear_combination h
      exact one_ne_zero this
    · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
      subst this
      have e : (45 / 5 : ℕ) = 9 := by norm_num
      rw [e]; exact hα9
  have hprim : IsPrimitiveRoot α 45 := hord ▸ IsPrimitiveRoot.orderOf α
  refine ⟨α, hprim, ?_⟩
  have hsub : (p.rootSet p.SplittingField) ⊆ (IntermediateField.adjoin (ZMod 7) {α}).toSubalgebra := by
    intro r hr
    have hr15 := (hmem r).1 hr
    have hr45 : r ^ 45 = 1 := by
      have : r^45 = (r^15)^3 := by ring
      rw [this, hr15]; linear_combination hchar
    obtain ⟨i, _, hi⟩ := hprim.eq_pow_of_pow_eq_one hr45
    rw [← hi]
    have hz : α ∈ IntermediateField.adjoin (ZMod 7) {α} := IntermediateField.subset_adjoin _ _ (Set.mem_singleton α)
    exact (pow_mem hz i : α ^ i ∈ IntermediateField.adjoin (ZMod 7) {α})
  rw [eq_top_iff]
  intro x _
  have h : x ∈ Algebra.adjoin (ZMod 7) (p.rootSet p.SplittingField) := by
    rw [SplittingField.adjoin_rootSet]; trivial
  have h3 := Algebra.adjoin_le hsub h
  exact h3
