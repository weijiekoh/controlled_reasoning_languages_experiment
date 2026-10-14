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
  let f : ℕ → ℤ → ZMod 2 := fun n a => if a ∈ S n then 1 else 0
  let T : (ℤ → ZMod 2) → (ℤ → ZMod 2) := fun u a => u a + u (a - 1)
  have hrec : ∀ n a, f (n+1) a = f n a + f n (a-1) := by
    intro n a
    have h := hSdef n a
    simp only [f]
    by_cases h1 : a - 1 ∈ S n <;> by_cases h2 : a ∈ S n <;>
      simp [h, h1, h2, Xor'] <;> decide
  have hT : ∀ n, f n = T^[n] (f 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← ih]
      funext a
      exact hrec n a
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hpow : ∀ k : ℕ, ∀ (u : ℤ → ZMod 2) (a : ℤ),
      (T^[2^k]) u a = u a + u (a - ((2^k : ℕ) : ℤ)) := by
    intro k
    induction k with
    | zero => intro u a; simp [T]
    | succ k ih =>
      intro u a
      rw [show 2^(k+1) = 2^k + 2^k by ring, Function.iterate_add_apply]
      simp only [ih]
      push_cast
      rw [show a - (2^k + 2^k) = a - 2^k - 2^k by ring]
      linear_combination (u (a - 2^k)) * h2
  have hBnd : ∃ B : ℤ, ∀ x ∈ S 0, x ≤ B := by
    obtain ⟨B, hB⟩ := (hSfin 0).bddAbove
    exact ⟨B, fun x hx => hB hx⟩
  intro n
  obtain ⟨B, hB⟩ := hBnd
  set K : ℕ := n + B.toNat with hKdef
  have hK1 : n ≤ K := Nat.le_add_right _ _
  have hK2 : K < 2^K := Nat.lt_two_pow_self
  have hK3 : B ≤ (K : ℤ) := by
    have := Int.self_le_toNat B
    omega
  have hNB : B < ((2^K : ℕ) : ℤ) := by
    push_cast
    have : (K:ℤ) < (2:ℤ)^K := by exact_mod_cast hK2
    omega
  refine ⟨2^K, ?_, ?_⟩
  · have : (n:ℤ) ≤ (K:ℤ) := by exact_mod_cast hK1
    have : (K:ℤ) < (2:ℤ)^K := by exact_mod_cast hK2
    have h3 : ((2^K : ℕ) : ℤ) = (2:ℤ)^K := by push_cast; ring
    omega
  · ext a
    have key : f (2^K) a = f 0 a + f 0 (a - ((2^K : ℕ) : ℤ)) := by
      rw [hT, hpow]
    have hdisj : a ∈ S 0 → a - ((2^K : ℕ) : ℤ) ∈ S 0 → False := fun h1 h2 => by
      have := hB a h1
      have := hSpos 0 a h1
      have := hSpos 0 _ h2
      omega
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases hA : a ∈ S 0 <;> by_cases hC : a - ((2^K : ℕ) : ℤ) ∈ S 0
    · exact (hdisj hA hC).elim
    · have hX : a ∈ S (2^K) := by
        by_contra h
        simp only [f, if_neg h, if_pos hA, if_neg hC] at key
        revert key; decide
      exact ⟨fun _ => Or.inl hA, fun _ => hX⟩
    · have hX : a ∈ S (2^K) := by
        by_contra h
        simp only [f, if_neg h, if_neg hA, if_pos hC] at key
        revert key; decide
      exact ⟨fun _ => Or.inr hC, fun _ => hX⟩
    · have hX : a ∉ S (2^K) := by
        intro h
        simp only [f, if_pos h, if_neg hA, if_neg hC] at key
        revert key; decide
      exact ⟨fun h => absurd h hX, fun h => (h.elim hA hC).elim⟩
