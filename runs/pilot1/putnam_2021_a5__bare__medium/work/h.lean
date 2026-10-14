import Mathlib

lemma key (p : ℕ) [Fact p.Prime] (hp : p ∣ 2021) (g : ℕ) (hg : Nat.Coprime g 2021)
    (hord : ∀ r < p - 1, ((g : ZMod p))^r = 1 → r = 0) (hcard : ((1932 : ℕ) : ZMod p) ≠ 0)
    (A : Finset ℕ) (hm : ∀ n, n ∈ A ↔ 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1) (j : ℕ) :
    (p ∣ ∑ n ∈ A, n ^ j) ↔ ¬ (p - 1) ∣ j := by
  have hAeq : A = (Finset.Icc 1 2021).filter (fun n => n.gcd 2021 = 1) := by
    ext n; rw [hm]; simp [and_assoc]
  have hcA : A.card = 1932 := by
    rw [hAeq]; decide +kernel
  have hpc : ∀ n ∈ A, Nat.Coprime n p := by
    intro n hn
    exact Nat.Coprime.coprime_dvd_right hp ((hm n).1 hn).2.2
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h hd
    obtain ⟨k, rfl⟩ := hd
    have : ∀ n ∈ A, ((n : ZMod p))^((p-1)*k) = 1 := by
      intro n hn
      have h0 : (n : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.Coprime.eq_one_of_dvd (hpc n hn).symm hd
        exact (Fact.out : p.Prime).one_lt.ne' this
      rw [pow_mul, ZMod.pow_card_sub_one_eq_one h0, one_pow]
    rw [Finset.sum_congr rfl this] at h
    simp [hcA] at h
    exact hcard (by exact_mod_cast h)
  · intro hd
