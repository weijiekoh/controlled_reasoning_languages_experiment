import Mathlib
open Finset
theorem L1 (j : ℕ) (A : Finset ℕ)
  (hA : A = {n | 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1}) :
  ((∑ n ∈ A, n ^ j : ℕ) : ZMod 2021) = ∑ u : (ZMod 2021)ˣ, ((u : ZMod 2021))^j := by
  haveI : Fact (1 < 2021) := ⟨by norm_num⟩
  have hm : ∀ n, n ∈ A ↔ 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1 := by
    intro n; have := Set.ext_iff.1 hA n; simpa using this
  symm
  push_cast
  refine Finset.sum_bij (fun u _ => (u : ZMod 2021).val) ?_ ?_ ?_ ?_
  · intro u _
    have h := ZMod.val_coe_unit_coprime u
    have h2 : (u : ZMod 2021).val < 2021 := ZMod.val_lt _
    have h3 : (u : ZMod 2021) ≠ 0 := u.ne_zero
    have h4 : (u : ZMod 2021).val ≠ 0 := by
      intro h0; exact h3 ((ZMod.val_eq_zero _).1 h0)
    rw [hm]
    refine ⟨by omega, by omega, h⟩
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective _ h)
  · intro n hn
    rw [hm] at hn
    have hc : Nat.Coprime n 2021 := Nat.coprime_iff_gcd_eq_one.2 hn.2.2
    refine ⟨ZMod.unitOfCoprime n hc, by simp, ?_⟩
    have : n ≠ 2021 := by
      intro h; rw [h] at hc; norm_num [Nat.Coprime] at hc
    simp [ZMod.val_natCast]
    omega
  · intro u _
    simp

theorem L2 (j : ℕ) : (∑ u : (ZMod 2021)ˣ, ((u : ZMod 2021))^j = 0) ↔ ¬(42 ∣ j) ∧ ¬(46 ∣ j) := by
  have n1 : (46 : ZMod 43) ≠ 0 := by decide
  have n2 : (42 : ZMod 47) ≠ 0 := by decide
  let e : ZMod 2021 ≃+* ZMod 43 × ZMod 47 := ZMod.chineseRemainder (by norm_num : Nat.Coprime 43 47)
  let f : (ZMod 2021)ˣ ≃* (ZMod 43)ˣ × (ZMod 47)ˣ :=
    (Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits
  have key : e (∑ u : (ZMod 2021)ˣ, ((u : ZMod 2021))^j)
      = ∑ p : (ZMod 43)ˣ × (ZMod 47)ˣ, (((p.1 : ZMod 43))^j, ((p.2 : ZMod 47))^j) := by
    rw [map_sum]
    refine Fintype.sum_equiv f.toEquiv _ _ ?_
    intro u
    rw [map_pow]
    rfl
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
  have h1 := FiniteField.sum_pow_units (ZMod 43) j
  have h2 := FiniteField.sum_pow_units (ZMod 47) j
  rw [← map_eq_zero_iff e e.injective, key, Fintype.sum_prod_type]
  simp only [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero, Finset.sum_const, Finset.card_univ, Fintype.card_units, ZMod.card, ← Finset.smul_sum, h1, h2]
  by_cases a : 42 ∣ j <;> by_cases b : 46 ∣ j <;> simp [a, b, n1, n2]
