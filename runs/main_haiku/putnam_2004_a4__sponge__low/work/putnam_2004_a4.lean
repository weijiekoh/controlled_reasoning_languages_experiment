import Mathlib

open Nat Topology Filter

-- Note: uses (ℕ → Fin n → ℝ) instead of (Fin N → Fin n → ℝ)
/--
Show that for any positive integer $n$ there is an integer $N$ such that the product $x_1x_2 \cdots x_n$ can be expressed identically in the form $x_1x_2 \cdots x_n=\sum_{i=1}^Nc_i(a_{i1}x_1+a_{i2}x_2+\cdots+a_{in}x_n)^n$ where the $c_i$ are rational numbers and each $a_{ij}$ is one of the numbers $-1,0,1$.
-/
theorem putnam_2004_a4
  (n : ℕ) (npos : n > 0)
  (x : Fin n → ℝ)
  (avals : ℕ → (ℕ → Fin n → ℝ) → Prop)
  (havals : ∀ N a, avals N a ↔ ∀ (i : Fin N) (j : Fin n), (a i j = -1 ∨ a i j = 0 ∨ a i j = 1)) :
  ∃ (N : ℕ) (c : Fin N → ℚ) (a : ℕ → Fin n → ℝ),
    avals N a ∧
    (∏ i : Fin n, x i) = ∑ i : Fin N, c i * (∑ j : Fin n, a i j * x j) ^ n := by
  classical
  obtain ⟨sg, hT, hF⟩ : ∃ sg : Bool → ℝ, sg true = 1 ∧ sg false = -1 :=
    ⟨fun t => if t then 1 else -1, by simp, by simp⟩
  have hsgc : ∀ t, sg t = 1 ∨ sg t = -1 := by
    intro t; cases t <;> simp [hT, hF]
  have hsq : ∀ b : Fin n → Bool, (∏ j, sg (b j)) * (∏ j, sg (b j)) = 1 := by
    intro b
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    rcases hsgc (b j) with h | h <;> simp [h]
  have hpow : ∀ m : ℕ, ∑ t : Bool, sg t ^ m = 1 + (-1) ^ m := by
    intro m; rw [Fintype.sum_bool, hT, hF]; simp
  have key : ∀ x : Fin n → ℝ, ((2:ℝ)^n * (Nat.factorial n : ℝ)) * ∏ i, x i
      = ∑ b : Fin n → Bool, (∏ j, sg (b j)) * (∑ j, sg (b j) * x j) ^ n := by
    intro x
    have h1 : ∀ b : Fin n → Bool, (∏ j, sg (b j)) * (∑ j, sg (b j) * x j) ^ n
        = ∑ k ∈ (Finset.univ : Finset (Fin n)).piAntidiag n,
            (∏ j, sg (b j)) * ((Nat.multinomial Finset.univ k : ℝ) * ∏ j, (sg (b j) * x j) ^ (k j)) := by
      intro b
      rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun b _ => h1 b), Finset.sum_comm]
    rw [Finset.sum_eq_single (fun _ : Fin n => 1)]
    · have hone : ∀ b : Fin n → Bool,
          (∏ j, sg (b j)) * ((Nat.multinomial Finset.univ (fun _ : Fin n => 1) : ℝ)
            * ∏ j, (sg (b j) * x j) ^ ((fun _ : Fin n => 1) j))
          = (Nat.factorial n : ℝ) * ∏ i, x i := by
        intro b
        have hm : Nat.multinomial Finset.univ (fun _ : Fin n => 1) = Nat.factorial n := by
          simp [Nat.multinomial]
        rw [hm]
        simp only [pow_one, Finset.prod_mul_distrib]
        have := hsq b
        calc _ = (Nat.factorial n : ℝ) * (((∏ j, sg (b j)) * (∏ j, sg (b j))) * ∏ i, x i) := by
              push_cast; ring
          _ = _ := by rw [this, one_mul]
      rw [Finset.sum_congr rfl (fun b _ => hone b)]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun] <;> ring
    · intro k hk hne
      have hterm : ∀ b : Fin n → Bool,
          (∏ j, sg (b j)) * ((Nat.multinomial Finset.univ k : ℝ) * ∏ j, (sg (b j) * x j) ^ (k j))
          = (Nat.multinomial Finset.univ k : ℝ) * ∏ j, (sg (b j) ^ (k j + 1) * x j ^ (k j)) := by
        intro b
        simp only [pow_succ, mul_pow, Finset.prod_mul_distrib]
        ring
      rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum,
        ← Fintype.prod_sum (fun j t => sg t ^ (k j + 1) * x j ^ (k j))]
      by_cases hall : ∀ j, Odd (k j)
      · exfalso
        apply hne
        obtain ⟨hsum, _⟩ := Finset.mem_piAntidiag.mp hk
        have hpos : ∀ j, 1 ≤ k j := fun j => (hall j).pos
        have heq : ∑ j : Fin n, (1:ℕ) = ∑ j, k j := by simp [hsum]
        have := (Finset.sum_eq_sum_iff_of_le (fun j _ => hpos j)).mp heq
        funext j
        exact (this j (Finset.mem_univ j)).symm
      · push_neg at hall
        obtain ⟨j, hj⟩ := hall
        rw [Finset.prod_eq_zero (Finset.mem_univ j) ?_, mul_zero]
        rw [← Finset.sum_mul, hpow, (Nat.not_odd_iff_even.mp hj).add_one.neg_one_pow]
        norm_num
    · intro hn
      exact absurd (Finset.mem_piAntidiag.mpr ⟨by simp, by simp⟩) hn
  let e : Fin (Fintype.card (Fin n → Bool)) ≃ (Fin n → Bool) := (Fintype.equivFin _).symm
  let cq : (Fin n → Bool) → ℚ := fun b =>
    (∏ j, (if b j then 1 else -1 : ℚ)) / (2 ^ n * (Nat.factorial n : ℚ))
  have hcq : ∀ b : Fin n → Bool, ((cq b : ℚ) : ℝ) = (∏ j, sg (b j)) / ((2:ℝ)^n * (Nat.factorial n : ℝ)) := by
    intro b
    have h2 : ∏ j, sg (b j) = ∏ j, (((if b j then 1 else -1 : ℚ)) : ℝ) :=
      Finset.prod_congr rfl (fun j _ => by cases b j <;> simp [hT, hF])
    simp only [cq]
    rw [h2]
    push_cast
    ring
  have hD : ((2:ℝ)^n * (Nat.factorial n : ℝ)) ≠ 0 := by positivity
  refine ⟨Fintype.card (Fin n → Bool), fun i => cq (e i),
    fun k j => if h : k < Fintype.card (Fin n → Bool) then sg (e ⟨k, h⟩ j) else 0, ?_, ?_⟩
  · rw [havals]
    intro i j
    have ha : (if h : (i:ℕ) < Fintype.card (Fin n → Bool) then sg (e ⟨i, h⟩ j) else 0) = sg (e i j) := by
      rw [dif_pos i.isLt]
    rw [ha]
    rcases hsgc (e i j) with h | h <;> simp [h]
  · have hval : ∀ (i : Fin (Fintype.card (Fin n → Bool))) (j : Fin n),
        (if h : (i:ℕ) < Fintype.card (Fin n → Bool) then sg (e ⟨i, h⟩ j) else 0) = sg (e i j) := by
      intro i j; rw [dif_pos i.isLt]
    simp only [hval]
    have fin : ∑ i : Fin (Fintype.card (Fin n → Bool)), ((cq (e i) : ℚ) : ℝ) * (∑ j, sg (e i j) * x j) ^ n
        = ∑ b, ((cq b : ℚ) : ℝ) * (∑ j, sg (b j) * x j) ^ n :=
      Equiv.sum_comp e (fun b => ((cq b : ℚ) : ℝ) * (∑ j, sg (b j) * x j) ^ n)
    rw [fin]
    have hsum : ∑ b, ((cq b : ℚ) : ℝ) * (∑ j, sg (b j) * x j) ^ n = ∏ i, x i := by
      rw [Finset.sum_congr rfl (fun b _ => show ((cq b : ℚ) : ℝ) * (∑ j, sg (b j) * x j) ^ n
          = (∏ j, sg (b j)) * (∑ j, sg (b j) * x j) ^ n / ((2:ℝ)^n * (Nat.factorial n : ℝ)) by
            rw [hcq b]; ring)]
      rw [← Finset.sum_div, ← key x, mul_div_cancel_left₀ _ hD]
    exact hsum.symm
