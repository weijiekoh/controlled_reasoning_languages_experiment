import Mathlib

open BigOperators Finset Matrix

/--
For $n \geq 2$, let $A = [a_{i,j}]_{i,j=1}^n$ be an $n$-by-$n$ matrix of nonnegative integers such that:
(a) $a_{i,j} = 0$ when $i + j \leq n$;
(b) $a_{i+1,j} \in \{a_{i,j}, a_{i,j} + 1\}$ when $1 \leq i \leq n-1$ and $1 \leq j \leq n$; and
(c) $a_{i,j+1} \in \{a_{i,j}, a_{i,j} + 1\}$ when $1 \leq i \leq n$ and $1 \leq j \leq n-1$.

Let $S$ be the sum of the entries of $A$, and let $N$ be the number of nonzero entries of $A$.
Prove that $S \leq \frac{(n+2)N}{3}$.
-/
theorem putnam_2025_b4
    (m : ℕ)
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℕ)
    (ha : ∀ (i j : Fin (m + 2)), (i : ℕ) + (j : ℕ) ≤ m → A i j = 0)
    (hb : ∀ (i : Fin (m + 1)) (j : Fin (m + 2)),
      A (Fin.succ i) j = A (Fin.castSucc i) j ∨
      A (Fin.succ i) j = A (Fin.castSucc i) j + 1)
    (hc : ∀ (i : Fin (m + 2)) (j : Fin (m + 1)),
      A i (Fin.succ j) = A i (Fin.castSucc j) ∨
      A i (Fin.succ j) = A i (Fin.castSucc j) + 1)
    (S : ℕ)
    (hS : S = ∑ i : Fin (m + 2), ∑ j : Fin (m + 2), A i j)
    (N : ℕ)
    (hN : N = #{p : Fin (m + 2) × Fin (m + 2) | A p.1 p.2 ≠ 0}) :
    3 * S ≤ (m + 4) * N := by
  have key : ∀ (n : ℕ), 2 ≤ n → ∀ (s : ℕ), s ≤ n → ∀ g : ℕ → ℕ → ℕ,
      (∀ i j, i+1<n → j<n → g (i+1) j = g i j ∨ g (i+1) j = g i j + 1) →
      (∀ i j, i<n → j+1<n → g i (j+1) = g i j ∨ g i (j+1) = g i j + 1) →
      (∀ i j, i<n → j<n → g i j ≠ 0 → 2*n ≤ i+j+1+s) →
      3 * ∑ i ∈ range n, ∑ j ∈ range n, g i j ≤
        (s+2) * ∑ i ∈ range n, ∑ j ∈ range n, (if g i j ≠ 0 then 1 else 0) := by
    intro n hn s
    induction s with
    | zero =>
      intro _ g _ _ hz
      have h0 : ∀ i ∈ range n, ∀ j ∈ range n, g i j = 0 := by
        intro i hi j hj
        by_contra h
        have := hz i j (mem_range.1 hi) (mem_range.1 hj) h
        have := mem_range.1 hi
        have := mem_range.1 hj
        omega
      have hS : ∑ i ∈ range n, ∑ j ∈ range n, g i j = 0 :=
        Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => h0 i hi j hj))
      rw [hS]; simp
    | succ s ih =>
      intro hs g hb hc hz
      have hs' : s ≤ n := by omega
      have h1 := ih hs' (fun i j => g i j - 1)
        (by
          intro i j hi hj
          try dsimp only
          rcases hb i j hi hj with h | h <;> omega)
        (by
          intro i j hi hj
          try dsimp only
          rcases hc i j hi hj with h | h <;> omega)
        (by
          intro i j hi hj hne
          try dsimp only at hne
          rcases i with _ | i
          · rcases j with _ | j
            · have := hz 0 0 hi hj (by omega); omega
            · have := hc 0 j hi hj
              have := hz 0 j hi (by omega) (by omega)
              omega
          · have := hb i j hi hj
            have := hz i j (by omega) hj (by omega)
            omega)
      try dsimp only at h1
      have hrow : ∀ i j, i < n → j < n → g i j ≠ 0 → (∀ k < j, g i k = 0) → g i j = 1 := by
        intro i j hi hj hne hk
        rcases j with _ | j
        · rcases i with _ | i
          · have := hz 0 0 hi hj hne; omega
          · have h0 : g i 0 = 0 := by
              by_contra hh
              have := hz i 0 (by omega) hj hh
              omega
            have := hb i 0 hi hj
            omega
        · have h0 := hk j (by omega)
          have := hc i j hi hj
          omega
      have hcol : ∀ i j, i < n → j < n → g i j ≠ 0 → (∀ k < i, g k j = 0) → g i j = 1 := by
        intro i j hi hj hne hk
        rcases i with _ | i
        · rcases j with _ | j
          · have := hz 0 0 hi hj hne; omega
          · have h0 : g 0 j = 0 := by
              by_contra hh
              have := hz 0 j hi (by omega) hh
              omega
            have := hc 0 j hi hj
            omega
        · have h0 := hk i (by omega)
          have := hb i j hi hj
          omega
      have rowpart : ∀ h : ℕ → ℕ → ℕ, ∑ i ∈ range n, ∑ j ∈ range n, (if h i j ≠ 0 then 1 else 0) ≤
          ∑ i ∈ range n, ∑ j ∈ range n, (if (h i j ≠ 0 ∧ ∀ k < j, h i k = 0) then n - j else 0) := by
        intro h
        apply Finset.sum_le_sum
        intro i _
        classical
        by_cases hex : ∃ j, j < n ∧ h i j ≠ 0
        · have hsp := Nat.find_spec hex
          have hmin : ∀ m, m < n ∧ h i m ≠ 0 → Nat.find hex ≤ m := fun m hm => Nat.find_min' hex hm
          have hL : ∑ j ∈ range n, (if h i j ≠ 0 then 1 else 0) ≤ n - Nat.find hex := by
            rw [← Finset.card_filter]
            calc (filter (fun j => h i j ≠ 0) (range n)).card ≤ (Ico (Nat.find hex) n).card := by
                  apply Finset.card_le_card
                  intro j hj
                  simp only [mem_filter, mem_range] at hj
                  simp only [mem_Ico]
                  exact ⟨hmin j hj, hj.1⟩
              _ = n - Nat.find hex := Nat.card_Ico _ _
          have hR : n - Nat.find hex ≤ ∑ j ∈ range n, (if (h i j ≠ 0 ∧ ∀ k < j, h i k = 0) then n - j else 0) := by
            have hc2 : (h i (Nat.find hex) ≠ 0 ∧ ∀ k < Nat.find hex, h i k = 0) := by
              refine ⟨hsp.2, ?_⟩
              intro k hk
              by_contra hh
              have := hmin k ⟨by omega, hh⟩
              omega
            have := Finset.single_le_sum (f := fun j => (if (h i j ≠ 0 ∧ ∀ k < j, h i k = 0) then n - j else 0))
              (fun _ _ => Nat.zero_le _) (mem_range.2 hsp.1)
            simp only [if_pos hc2] at this
            exact this
          omega
        · have : ∀ j ∈ range n, (if h i j ≠ 0 then 1 else 0) = 0 := by
            intro j hj
            have : h i j = 0 := by
              by_contra hh
              exact hex ⟨j, mem_range.1 hj, hh⟩
            simp [this]
          rw [Finset.sum_eq_zero this]
          exact Nat.zero_le _
      have K : 2 * (∑ i ∈ range n, ∑ j ∈ range n, (if g i j ≠ 0 then 1 else 0)) ≤
          (s+2) * ∑ i ∈ range n, ∑ j ∈ range n, (if g i j = 1 then 1 else 0) := by
        have r1 := rowpart g
        have r2 := rowpart (fun a b => g b a)
        try dsimp only at r2
        have e1 : ∑ a ∈ range n, ∑ b ∈ range n, (if g b a ≠ 0 then 1 else 0) =
            ∑ i ∈ range n, ∑ j ∈ range n, (if g i j ≠ 0 then 1 else 0) := Finset.sum_comm
        have e2 : ∑ a ∈ range n, ∑ b ∈ range n, (if (g b a ≠ 0 ∧ ∀ k < b, g k a = 0) then n - b else 0) =
            ∑ i ∈ range n, ∑ j ∈ range n, (if (g i j ≠ 0 ∧ ∀ k < i, g k j = 0) then n - i else 0) :=
          Finset.sum_comm
        rw [e1, e2] at r2
        have pw : ∀ i j, i < n → j < n →
            (if (g i j ≠ 0 ∧ ∀ k < j, g i k = 0) then n - j else 0) +
            (if (g i j ≠ 0 ∧ ∀ k < i, g k j = 0) then n - i else 0) ≤
              (s+2) * (if g i j = 1 then 1 else 0) := by
          intro i j hi hj
          by_cases hg0 : g i j = 0
          · simp [hg0]
          · have hzz := hz i j hi hj hg0
            by_cases c1 : ∀ k < j, g i k = 0
            · have h1 := hrow i j hi hj hg0 c1
              by_cases c2 : ∀ k < i, g k j = 0
              · rw [if_pos ⟨hg0, c1⟩, if_pos ⟨hg0, c2⟩, if_pos h1]; omega
              · rw [if_pos ⟨hg0, c1⟩, if_neg (fun h => c2 h.2), if_pos h1]; omega
            · by_cases c2 : ∀ k < i, g k j = 0
              · have h1 := hcol i j hi hj hg0 c2
                rw [if_neg (fun h => c1 h.2), if_pos ⟨hg0, c2⟩, if_pos h1]; omega
              · rw [if_neg (fun h => c1 h.2), if_neg (fun h => c2 h.2)]; simp
        have comb : ∑ i ∈ range n, ∑ j ∈ range n,
            ((if (g i j ≠ 0 ∧ ∀ k < j, g i k = 0) then n - j else 0) +
            (if (g i j ≠ 0 ∧ ∀ k < i, g k j = 0) then n - i else 0)) ≤
            (s+2) * ∑ i ∈ range n, ∑ j ∈ range n, (if g i j = 1 then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j hj
          exact pw i j (mem_range.1 hi) (mem_range.1 hj)
        have hsplit : ∑ i ∈ range n, ∑ j ∈ range n,
            ((if (g i j ≠ 0 ∧ ∀ k < j, g i k = 0) then n - j else 0) +
            (if (g i j ≠ 0 ∧ ∀ k < i, g k j = 0) then n - i else 0)) =
            ∑ i ∈ range n, ∑ j ∈ range n, (if (g i j ≠ 0 ∧ ∀ k < j, g i k = 0) then n - j else 0) +
            ∑ i ∈ range n, ∑ j ∈ range n, (if (g i j ≠ 0 ∧ ∀ k < i, g k j = 0) then n - i else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_add_distrib]
        omega
      have hSum : ∑ i ∈ range n, ∑ j ∈ range n, g i j =
          ∑ i ∈ range n, ∑ j ∈ range n, (g i j - 1) +
          ∑ i ∈ range n, ∑ j ∈ range n, (if g i j ≠ 0 then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> omega
      have hN : ∑ i ∈ range n, ∑ j ∈ range n, (if g i j ≠ 0 then 1 else 0) =
          ∑ i ∈ range n, ∑ j ∈ range n, (if g i j - 1 ≠ 0 then 1 else 0) +
          ∑ i ∈ range n, ∑ j ∈ range n, (if g i j = 1 then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> omega
      rw [hSum]
      rw [hN] at K ⊢
      nlinarith [h1, K]
  obtain ⟨g, hgA⟩ : ∃ g : ℕ → ℕ → ℕ, ∀ i j : Fin (m+2), g i j = A i j :=
    ⟨fun i j => if h : i < m+2 then (if h' : j < m+2 then A ⟨i,h⟩ ⟨j,h'⟩ else 0) else 0,
      by intro i j; simp [i.isLt, j.isLt]⟩
  have hS' : ∑ i ∈ range (m+2), ∑ j ∈ range (m+2), g i j = S := by
    rw [hS, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    exact hgA i j
  have hN' : ∑ i ∈ range (m+2), ∑ j ∈ range (m+2), (if g i j ≠ 0 then 1 else 0) = N := by
    rw [hN, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [hgA i j]
  have := key (m+2) (by omega) (m+2) le_rfl g
    (by
      intro i j hi hj
      have e1 : g (i+1) j = A (Fin.succ ⟨i, by omega⟩) ⟨j,hj⟩ := hgA (Fin.succ ⟨i, by omega⟩) ⟨j,hj⟩
      have e2 : g i j = A (Fin.castSucc ⟨i, by omega⟩) ⟨j,hj⟩ := hgA (Fin.castSucc ⟨i, by omega⟩) ⟨j,hj⟩
      rw [e1, e2]
      exact hb ⟨i, by omega⟩ ⟨j,hj⟩)
    (by
      intro i j hi hj
      have e1 : g i (j+1) = A ⟨i,hi⟩ (Fin.succ ⟨j, by omega⟩) := hgA ⟨i,hi⟩ (Fin.succ ⟨j, by omega⟩)
      have e2 : g i j = A ⟨i,hi⟩ (Fin.castSucc ⟨j, by omega⟩) := hgA ⟨i,hi⟩ (Fin.castSucc ⟨j, by omega⟩)
      rw [e1, e2]
      exact hc ⟨i,hi⟩ ⟨j, by omega⟩)
    (by
      intro i j hi hj hne
      by_contra hh
      apply hne
      rw [show g i j = A ⟨i,hi⟩ ⟨j,hj⟩ from hgA ⟨i,hi⟩ ⟨j,hj⟩]
      exact ha _ _ (by show i + j ≤ m; omega))
  rw [hS', hN'] at this
  linarith
