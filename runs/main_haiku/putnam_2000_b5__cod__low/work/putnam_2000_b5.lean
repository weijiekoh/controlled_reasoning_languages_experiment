import Mathlib

open Topology Filter Nat Set Function

/--
Let $S_0$ be a finite set of positive integers. We define finite sets $S_1,S_2,\ldots$ of positive integers as follows: the integer $a$ is in $S_{n+1}$ if and only if exactly one of $a-1$ or $a$ is in $S_n$. Show that there exist infinitely many integers $N$ for which $S_N=S_0\cup\{N+a: a\in S_0\}$.
-/
theorem putnam_2000_b5
(S : ℕ → Set ℤ)
(hSfin : ∀ n, Set.Finite (S n))
(hSpos : ∀ n, ∀ s ∈ S n, s > 0)
(hSdef : ∀ n, ∀ a, a ∈ S (n + 1) ↔ Xor' (a - 1 ∈ S n) (a ∈ S n))
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) :=
by
  classical
  obtain ⟨B, hB⟩ := (hSfin 0).bddAbove
  have hB' : ∀ s ∈ S 0, s ≤ B := fun s hs => hB hs
  have hneg : ∀ k (x : ℤ), x ≤ 0 → x ∉ S k := fun k x hx h => by
    have := hSpos k x h; omega
  let T : ℕ → Finset ℕ := fun n => ((hSfin n).toFinset).image Int.toNat
  let Q : ℕ → Polynomial (ZMod 2) := fun n => ∑ m ∈ T n, Polynomial.X ^ m
  have hmem : ∀ n m, m ∈ T n ↔ (m : ℤ) ∈ S n := by
    intro n m
    simp only [T, Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hSpos n x hx
      rw [Int.toNat_of_nonneg this.le]; exact hx
    · intro h; exact ⟨(m : ℤ), h, by simp⟩
  have hcoeffQ : ∀ n m, (Q n).coeff m = if (m : ℤ) ∈ S n then 1 else 0 := by
    intro n m
    simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [hmem]
  have hrec : ∀ n, Q (n + 1) = (1 + Polynomial.X) * Q n := by
    intro n
    ext m
    rw [add_mul, one_mul, Polynomial.coeff_add, hcoeffQ, hcoeffQ]
    rcases m with _ | k
    · have e1 : (0 : ℤ) ∉ S n := hneg n 0 le_rfl
      have e2 : (0 : ℤ) ∉ S (n + 1) := by
        intro h
        have a1 := hneg n (0 - 1) (by norm_num)
        have := (hSdef n 0).1 h
        simp only [Xor', a1, e1, false_iff, not_false_eq_true, and_false, false_and, or_false, false_or] at this

        simp_all
      rw [Polynomial.coeff_X_mul_zero]
      simp [e1, e2]
    · rw [Polynomial.coeff_X_mul]
      have hk := hSdef n ((k + 1 : ℕ) : ℤ)
      have hh : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [hh] at hk
      by_cases h1 : (k : ℤ) ∈ S n <;> by_cases h2 : ((k + 1 : ℕ) : ℤ) ∈ S n <;>
        by_cases h3 : ((k + 1 : ℕ) : ℤ) ∈ S (n + 1) <;> simp_all [Xor'] <;> decide
  have hpow : ∀ n, Q n = (1 + Polynomial.X) ^ n * Q 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hrec, ih, pow_succ]; ring
  have hfrob : ∀ k, Q (2 ^ k) = (1 + Polynomial.X ^ (2 ^ k)) * Q 0 := by
    intro k; rw [hpow, add_pow_char_pow]; simp
  have hcoefN : ∀ k m, (Q (2 ^ k)).coeff m
      = (Q 0).coeff m + if 2 ^ k ≤ m then (Q 0).coeff (m - 2 ^ k) else 0 := by
    intro k m
    rw [hfrob, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
  intro n
  let t := B.toNat
  have hBt : B ≤ (t : ℤ) := Int.self_le_toNat B
  have hnt : n < 2 ^ (n + t) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have htN : t < 2 ^ (n + t) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨2 ^ (n + t), by omega, ?_⟩
  have key := hcoefN (n + t)
  generalize hNdef : 2 ^ (n + t) = N at hnt htN key ⊢
  ext M
  simp only [Set.mem_union, Set.mem_setOf_eq]
  rcases le_or_gt M 0 with hM | hM
  · constructor
    · intro h; exact absurd h (hneg _ _ hM)
    · rintro (h | h)
      · exact absurd h (hneg 0 _ hM)
      · exact absurd h (hneg 0 _ (by omega))
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = m := ⟨M.toNat, (Int.toNat_of_nonneg hM.le).symm⟩
    have hc := hcoeffQ N m
    rw [key, hcoeffQ, hcoeffQ] at hc
    by_cases hA : (m : ℤ) ∈ S 0
    · have hlt : ¬ (N ≤ m) := by
        intro hle
        have := hB' _ hA
        omega
      rw [if_neg hlt, add_zero] at hc
      by_cases hS : (m : ℤ) ∈ S N
      · simp [hS, hA]
      · simp [hS] at hc
        simp [hS, hA] at hc ⊢
    · by_cases hB2 : (m : ℤ) - N ∈ S 0
      · have hle : N ≤ m := by
          by_contra hc'
          exact hneg 0 ((m : ℤ) - N) (by omega) hB2
        rw [if_pos hle, Nat.cast_sub hle] at hc
        by_cases hS : (m : ℤ) ∈ S N
        · simp [hS, hA, hB2] at hc ⊢
        · simp [hS, hA, hB2] at hc ⊢
      · by_cases hle : N ≤ m
        · rw [if_pos hle, Nat.cast_sub hle] at hc
          by_cases hS : (m : ℤ) ∈ S N
          · simp [hS, hA, hB2] at hc ⊢
          · simp [hS, hA, hB2] at hc ⊢
        · rw [if_neg hle, add_zero] at hc
          by_cases hS : (m : ℤ) ∈ S N
          · simp [hS, hA, hB2] at hc ⊢
          · simp [hS, hA, hB2] at hc ⊢
