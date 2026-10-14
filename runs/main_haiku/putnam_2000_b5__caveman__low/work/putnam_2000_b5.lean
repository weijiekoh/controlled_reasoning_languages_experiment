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
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Polynomial (ZMod 2),
      ∀ n, F n = ∑ a ∈ (hSfin n).toFinset, Polynomial.X ^ a.toNat := ⟨_, fun n => rfl⟩
  have hcoeff : ∀ n (k : ℕ), (F n).coeff k = if (k:ℤ) ∈ S n then 1 else 0 := by
    intro n k
    rw [hF, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_X_pow]
    split_ifs with hk
    · rw [Finset.sum_eq_single_of_mem (k:ℤ) (by simpa using hk)]
      · simp
      · intro b hb hne
        have hb0 := hSpos n b (by simpa using hb)
        have : k ≠ b.toNat := by intro h; apply hne; omega
        simp [this]
    · apply Finset.sum_eq_zero
      intro a ha
      have ha' : a ∈ S n := by simpa using ha
      have hpa := hSpos n a ha'
      have : k ≠ a.toNat := by
        intro h; apply hk; rw [show (k:ℤ) = a by omega]; exact ha'
      simp [this]
  have hX : ∀ n (k : ℕ), (Polynomial.X * F n).coeff k = if ((k:ℤ) - 1) ∈ S n then 1 else 0 := by
    intro n k
    cases k with
    | zero =>
      rw [Polynomial.coeff_X_mul_zero, if_neg]
      intro h
      have := hSpos n _ h
      norm_num at this
    | succ m =>
      rw [Polynomial.coeff_X_mul, hcoeff]
      have : ((m+1:ℕ):ℤ) - 1 = (m:ℤ) := by push_cast; ring
      rw [this]
  have hstep : ∀ n, F (n+1) = (1 + Polynomial.X) * F n := by
    intro n
    ext k
    rw [add_mul, one_mul, Polynomial.coeff_add, hcoeff, hcoeff, hX]
    by_cases P : ((k:ℤ) - 1) ∈ S n <;> by_cases Q : ((k:ℤ)) ∈ S n <;>
      simp only [hSdef n k, Xor, P, Q, if_true, if_false, true_and, and_true, false_and, and_false,
        not_true_eq_false, not_false_eq_true, or_false, false_or, true_or, or_true, Xor'] <;>
      decide
  have hpow : ∀ n, F n = (1 + Polynomial.X) ^ n * F 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hstep, ih, pow_succ]; ring
  have hN : ∀ m, F (2^m) = F 0 + Polynomial.X ^ (2^m) * F 0 := by
    intro m
    rw [hpow, add_pow_char_pow, one_pow]
    ring
  -- bound on S 0
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ a ∈ S 0, a.toNat ≤ B :=
    ⟨∑ a ∈ (hSfin 0).toFinset, a.toNat, fun a ha =>
      Finset.single_le_sum (f := fun a : ℤ => a.toNat) (fun _ _ => Nat.zero_le _)
        ((hSfin 0).mem_toFinset.2 ha)⟩
  intro n
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = 2^(n+B) := ⟨_, rfl⟩
  have hNlt : n + B < N := by rw [hNdef]; exact Nat.lt_two_pow_self
  have hFN : F N = F 0 + Polynomial.X ^ N * F 0 := by rw [hNdef]; exact hN _
  have hbound : ∀ a ∈ S 0, a < (N:ℤ) := by
    intro a ha
    have := hB a ha
    have := hSpos 0 a ha
    omega
  have hint : ∀ k : ℕ, (if (k:ℤ) ∈ S N then (1 : ZMod 2) else 0) =
      (if (k:ℤ) ∈ S 0 then 1 else 0) +
        (if N ≤ k then (if ((k - N : ℕ) : ℤ) ∈ S 0 then 1 else 0) else 0) := by
    intro k
    have e := congrArg (fun p => Polynomial.coeff p k) hFN
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', hcoeff] at e
    exact e
  have key : ∀ k : ℕ, (k:ℤ) ∈ S N ↔ ((k:ℤ) ∈ S 0 ∨ (k:ℤ) - N ∈ S 0) := by
    intro k
    have e := hint k
    have hdisj : (k:ℤ) ∈ S 0 → (k:ℤ) - N ∈ S 0 → False := fun h1 h2 => by
      have := hSpos _ _ h2
      have := hbound _ h1
      omega
    by_cases hNk : N ≤ k
    · rw [if_pos hNk, Nat.cast_sub hNk] at e
      by_cases h1 : (k:ℤ) ∈ S 0 <;> by_cases h2 : (k:ℤ) - N ∈ S 0 <;>
        by_cases h3 : (k:ℤ) ∈ S N <;>
        simp only [h1, h2, h3, if_true, if_false, true_or, or_true, false_or, or_false,
          iff_true, iff_false, true_iff, false_iff, not_true, not_false_eq_true] at e ⊢ <;>
        first | decide | (exfalso; revert e; decide) | (revert e; decide) | (exfalso; exact hdisj h1 h2)
    · rw [if_neg hNk] at e
      have h2 : (k:ℤ) - N ∉ S 0 := fun h => by
        have := hSpos _ _ h
        omega
      by_cases h1 : (k:ℤ) ∈ S 0 <;> by_cases h3 : (k:ℤ) ∈ S N <;>
        simp only [h1, h2, h3, if_true, if_false, true_or, or_true, false_or, or_false,
          iff_true, iff_false, true_iff, false_iff, not_true, not_false_eq_true] at e ⊢ <;>
        first | decide | (exfalso; revert e; decide) | (revert e; decide)
  refine ⟨N, by omega, ?_⟩
  ext M
  rcases lt_or_ge M 0 with hM | hM
  · have h1 : M ∉ S N := fun h => by have := hSpos _ _ h; omega
    have h2 : M ∉ S 0 := fun h => by have := hSpos _ _ h; omega
    have h3 : M - N ∉ S 0 := fun h => by have := hSpos _ _ h; omega
    simp [h1, h2, h3]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, M = (k:ℤ) := ⟨M.toNat, by omega⟩
    simp only [Set.mem_union, Set.mem_setOf_eq]
    exact key k
