import Mathlib

open Filter Topology

noncomputable abbrev putnam_1997_a6_solution : ℤ → ℤ → ℝ := fun n k => Nat.choose (n.toNat-1) (k.toNat-1)
/--
For a positive integer $n$ and any real number $c$, define $x_k$ recursively by $x_0=0$, $x_1=1$, and for $k\geq 0$, \[x_{k+2}=\frac{cx_{k+1}-(n-k)x_k}{k+1}.\] Fix $n$ and then take $c$ to be the largest value for which $x_{n+1}=0$. Find $x_k$ in terms of $n$ and $k$, $1\leq k\leq n$.
-/
theorem putnam_1997_a6
  (n : ℤ)
  (hn : n > 0)
  (x : ℝ → (ℤ → ℝ))
  (hx0 : ∀ c, x c 0 = 0)
  (hx1 : ∀ c, x c 1 = 1)
  (hxk : ∀ c, ∀ k ≥ 0, x c (k + 2) = (c*(x c (k + 1)) - (n - k)*(x c k))/(k + 1))
  (S : Set ℝ)
  (hS : S = {c : ℝ | x c (n + 1) = 0}) :
  ∀ k : Set.Icc 1 n, x (sSup S) k = putnam_1997_a6_solution n k :=
by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m:ℤ) + 1 := ⟨(n-1).toNat, by omega⟩
  have hrec : ∀ c : ℝ, ∀ j : ℕ, x c ((j:ℤ)+3) = (c * x c ((j:ℤ)+2) - (m - j) * x c ((j:ℤ)+1)) / (j+2) := by
    intro c j
    have := hxk c ((j:ℤ)+1) (by omega)
    have e1 : (j:ℤ)+1+2 = (j:ℤ)+3 := by ring
    have e2 : (j:ℤ)+1+1 = (j:ℤ)+2 := by ring
    rw [e1, e2] at this
    rw [this]; push_cast; ring_nf
  have hmain : ∀ j : ℕ, x (m:ℝ) ((j:ℤ)+1) = (m.choose j : ℝ) ∧ x (m:ℝ) ((j:ℤ)+2) = (m.choose (j+1) : ℝ) := by
    intro j
    induction j with
    | zero =>
      have h2 := hxk (m:ℝ) 0 le_rfl
      simp [hx0, hx1] at h2 ⊢
      exact h2
    | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨by push_cast; rw [← h2]; ring_nf, ?_⟩
      have := hrec (m:ℝ) j
      have e : ((j+1:ℕ):ℤ)+2 = (j:ℤ)+3 := by push_cast; ring
      rw [e, this, h1, h2, div_eq_iff (by positivity)]
      rcases le_or_gt (j+1) m with h | h
      · have i1 := Nat.choose_succ_right_eq m j
        have i2 := Nat.choose_succ_right_eq m (j+1)
        have i1' : (m.choose (j+1) : ℝ) * (j+1) = m.choose j * (m - j) := by
          have := congrArg (fun t : ℕ => (t:ℝ)) i1
          simp only [Nat.cast_mul] at this
          rw [Nat.cast_sub (by omega)] at this
          exact_mod_cast this
        have i2' : (m.choose (j+1+1) : ℝ) * (j+1+1) = m.choose (j+1) * (m - (j+1)) := by
          have := congrArg (fun t : ℕ => (t:ℝ)) i2
          simp only [Nat.cast_mul] at this
          rw [Nat.cast_sub (by omega)] at this
          exact_mod_cast this
        push_cast
        linear_combination i1' - i2'
      · have b0 : m.choose (j+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have c0 : m.choose (j+1+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [b0, c0]
        rcases Nat.eq_or_lt_of_le (show m ≤ j by omega) with h' | h'
        · subst h'; simp
        · rw [Nat.choose_eq_zero_of_lt h']; simp
  have hS1 : (m:ℝ) ∈ S := by
    rw [hS]
    show x (m:ℝ) ((m:ℤ)+1+1) = 0
    have h := (hmain (m+1)).1
    push_cast at h
    rw [h]; simp
  have hub : ∀ c : ℝ, c > m → c ∉ S := by
    intro c hc hcS
    rw [hS] at hcS
    have key : ∀ j : ℕ, j + 1 ≤ m + 1 → 0 < x c ((j:ℤ)+1) ∧ ((j:ℝ)+1) * x c ((j:ℤ)+2) > ((m:ℝ) - j) * x c ((j:ℤ)+1) := by
      intro j
      induction j with
      | zero =>
        intro _
        have h2 := hxk c 0 le_rfl
        simp [hx0, hx1] at h2 ⊢
        rw [h2]; exact hc
      | succ j ih =>
        intro hj
        obtain ⟨p, q⟩ := ih (by omega)
        have hjm : (j:ℝ) ≤ m := by exact_mod_cast (by omega : j ≤ m)
        have x1 : 0 < x c ((j:ℤ)+2) := by
          by_contra hneg
          push_neg at hneg
          nlinarith [mul_nonneg (sub_nonneg.2 hjm) p.le, (by positivity : (0:ℝ) < (j:ℝ)+1)]
        have := hrec c j
        have e : ((j+1:ℕ):ℤ)+1 = (j:ℤ)+2 := by push_cast; ring
        have e2 : ((j+1:ℕ):ℤ)+2 = (j:ℤ)+3 := by push_cast; ring
        rw [e, e2]
        refine ⟨x1, ?_⟩
        rw [this]
        push_cast
        have : ((j:ℝ)+1+1) * ((c * x c ((j:ℤ)+2) - (m - j) * x c ((j:ℤ)+1)) / (j+2)) = c * x c ((j:ℤ)+2) - (m - j) * x c ((j:ℤ)+1) := by
          field_simp; ring
        rw [this]
        nlinarith
    have h3 := (key m le_rfl).2
    have : x c ((m:ℤ)+2) = x c ((m:ℤ)+1+1) := by ring_nf
    rw [this, hcS] at h3
    simp at h3
  have hsup : sSup S = m := by
    apply le_antisymm
    · apply csSup_le ⟨_, hS1⟩
      intro c hc
      by_contra h
      exact hub c (not_le.1 h) hc
    · exact le_csSup ⟨m, fun c hc => by
        by_contra h
        exact hub c (not_le.1 h) hc⟩ hS1
  rintro ⟨k, hk1, hk2⟩
  rw [hsup]
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j:ℤ)+1 := ⟨(k-1).toNat, by omega⟩
  have := (hmain j).1
  simp only [putnam_1997_a6_solution]
  rw [this]
  congr 1
  all_goals omega
