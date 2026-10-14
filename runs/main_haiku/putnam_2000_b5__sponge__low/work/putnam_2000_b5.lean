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
  have hrec : ∀ n a, decide (a ∈ S (n+1)) = xor (decide (a ∈ S n)) (decide (a - 1 ∈ S n)) := by
    intro n a
    have h := hSdef n a
    by_cases h1 : a - 1 ∈ S n <;> by_cases h2 : a ∈ S n <;> simp_all [Xor']
  have hpow : ∀ k : ℕ, ∀ n a, decide (a ∈ S (n + 2^k)) = xor (decide (a ∈ S n)) (decide (a - ((2^k:ℕ):ℤ) ∈ S n)) := by
    intro k
    induction k with
    | zero =>
      intro n a
      simp only [pow_zero, Nat.cast_one]
      exact hrec n a
    | succ k ih =>
      intro n a
      have e1 : n + 2^(k+1) = (n + 2^k) + 2^k := by ring
      have e2 : a - ((2^(k+1):ℕ):ℤ) = (a - ((2^k:ℕ):ℤ)) - ((2^k:ℕ):ℤ) := by push_cast; ring
      rw [e1, ih, ih n a, ih n (a - ((2^k:ℕ):ℤ)), e2]
      generalize decide (a ∈ S n) = x
      generalize decide (a - ((2^k:ℕ):ℤ) ∈ S n) = y
      generalize decide ((a - ((2^k:ℕ):ℤ)) - ((2^k:ℕ):ℤ) ∈ S n) = z
      cases x <;> cases y <;> cases z <;> rfl
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ s ∈ S 0, s ≤ M := by
    obtain ⟨b, hb⟩ := (hSfin 0).bddAbove
    exact ⟨b, fun s hs => hb hs⟩
  intro n
  refine ⟨2^(n + M.toNat), ?_, ?_⟩
  · have := Nat.lt_two_pow_self (n := n + M.toNat)
    omega
  · have hNM : M ≤ ((2^(n + M.toNat):ℕ):ℤ) := by
      have h1 := Int.self_le_toNat M
      have h2 := Nat.lt_two_pow_self (n := n + M.toNat)
      have h3 : ((n + M.toNat : ℕ):ℤ) < ((2^(n + M.toNat):ℕ):ℤ) := by exact_mod_cast h2
      push_cast at h3 ⊢
      omega
    have hdisj : ∀ a, a ∈ S 0 → a - ((2^(n + M.toNat):ℕ):ℤ) ∉ S 0 := by
      intro a h1 h2
      have h3 := hSpos 0 _ h2
      have h4 := hM a h1
      omega
    ext a
    have h := hpow (n + M.toNat) 0 a
    rw [zero_add] at h
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases p : a ∈ S 0 <;> by_cases q : a - ((2^(n + M.toNat):ℕ):ℤ) ∈ S 0
    · exact absurd q (hdisj a p)
    · have hp' := decide_eq_true p
      have hq' := decide_eq_false q
      rw [hp', hq'] at h
      simp at h
      simp [p, h]
    · have hp' := decide_eq_false p
      have hq' := decide_eq_true q
      rw [hp', hq'] at h
      simp at h
      exact ⟨fun _ => Or.inr q, fun _ => h⟩
    · have hp' := decide_eq_false p
      have hq' := decide_eq_false q
      rw [hp', hq'] at h
      simp at h
      exact ⟨fun h' => absurd h' h, fun hr => absurd hr (not_or.mpr ⟨p, q⟩)⟩
