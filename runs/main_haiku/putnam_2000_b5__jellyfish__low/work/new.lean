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
  obtain ⟨B, hB⟩ := (hSfin 0).bddAbove
  have hC : ∀ k : ℕ, ∀ n : ℕ, ∀ a : ℤ,
      a ∈ S (n + 2^k) ↔ Xor' (a ∈ S n) (a - (2:ℤ)^k ∈ S n) := by
    intro k
    induction k with
    | zero =>
      intro n a
      simp only [pow_zero]
      rw [hSdef n a]
      unfold Xor' Xor
      tauto
    | succ k ih =>
      intro n a
      have e : n + 2^(k+1) = (n + 2^k) + 2^k := by ring
      have e2 : a - (2:ℤ)^k - (2:ℤ)^k = a - (2:ℤ)^(k+1) := by ring
      rw [e, ih (n + 2^k) a, ih n a, ih n (a - (2:ℤ)^k), e2]
      unfold Xor' Xor
      tauto
  have hpos : ∀ x, x ∈ S 0 → 0 < x := hSpos 0
  intro n
  set k := n + B.toNat + 1 with hk
  have hlt : k < 2^k := Nat.lt_two_pow_self
  refine ⟨2^k, ?_, ?_⟩
  · omega
  · have hBk : B < (2:ℤ)^k := by
      have h1 := Int.self_le_toNat B
      have h2 : ((k:ℕ):ℤ) < ((2^k:ℕ):ℤ) := by exact_mod_cast hlt
      push_cast at h2
      omega
    have key : ∀ a : ℤ, a ∈ S 0 → a - (2:ℤ)^k ∉ S 0 := by
      intro a h1 h2
      have := hpos _ h2
      have := hB h1
      omega
    ext a
    have hca := hC k 0 a
    rw [zero_add] at hca
    simp only [Set.mem_union, Set.mem_setOf_eq]
    push_cast
    rw [hca]
    unfold Xor' Xor
    have := key a
    tauto
