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
    (∏ i : Fin n, x i) = ∑ i : Fin N, c i * (∑ j : Fin n, a i j * x j) ^ n :=
by
  classical
  obtain ⟨sg, hsg⟩ : ∃ sg : Bool → ℝ, sg = fun b => if b then 1 else -1 := ⟨_, rfl⟩
  have hsg_pow : ∀ k : ℕ, ∑ b : Bool, sg b ^ (k+1) = if Even k then 0 else 2 := by
    intro k
    rcases Nat.even_or_odd k with h | h
    · have h1 : Odd (k+1) := h.add_one
      simp [hsg, h, h1.neg_one_pow]
    · have h1 : Even (k+1) := h.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr h
      simp [hsg, h2, h1.neg_one_pow]
  have hk : ∀ k : Fin n → ℕ, ∑ s : Fin n → Bool, (∏ j, sg (s j)) *
      ((Nat.multinomial Finset.univ k : ℝ) * ∏ j, (sg (s j) * x j) ^ (k j))
      = (Nat.multinomial Finset.univ k : ℝ) * ∏ j, ((if Even (k j) then 0 else 2) * x j ^ (k j)) := by
    intro k
    have hterm : ∀ s : Fin n → Bool, (∏ j, sg (s j)) * ((Nat.multinomial Finset.univ k : ℝ)
        * ∏ j, (sg (s j) * x j) ^ (k j))
        = (Nat.multinomial Finset.univ k : ℝ) * ∏ j, (sg (s j) ^ (k j + 1) * x j ^ (k j)) := by
      intro s
      rw [mul_left_comm, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [mul_pow, pow_succ]; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    have hp := Fintype.prod_sum (fun (j : Fin n) (b : Bool) => sg b ^ (k j + 1) * x j ^ (k j))
    rw [← hp]
    simp_rw [← Finset.sum_mul, hsg_pow]
  have key : ∑ s : Fin n → Bool, (∏ j, sg (s j)) * (∑ j, sg (s j) * x j) ^ n
      = 2^n * (n.factorial : ℝ) * ∏ j, x j := by
    have h1 : ∀ s : Fin n → Bool, (∑ j, sg (s j) * x j) ^ n
        = ∑ k ∈ (Finset.univ : Finset (Fin n)).piAntidiag n,
            (Nat.multinomial Finset.univ k : ℝ) * ∏ j, (sg (s j) * x j) ^ (k j) :=
      fun s => Finset.sum_pow_eq_sum_piAntidiag _ _ _
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun k _ => hk k)]
    rw [Finset.sum_eq_single (fun _ : Fin n => 1)]
    · have hm : Nat.multinomial Finset.univ (fun _ : Fin n => 1) = n.factorial := by
        have := Nat.multinomial_spec Finset.univ (fun _ : Fin n => 1)
        simpa using this
      rw [hm]
      simp [Finset.prod_mul_distrib]
      ring
    · intro k hk' hne
      have : ∃ j, Even (k j) := by
        by_contra hodd
        push Not at hodd
        apply hne
        have hs := (Finset.mem_piAntidiag.mp hk').1
        have hge : ∀ j ∈ (Finset.univ : Finset (Fin n)), 1 ≤ k j := fun j _ =>
          Nat.pos_of_ne_zero (fun h0 => hodd j (by rw [h0]; exact ⟨0, rfl⟩))
        have heq := (Finset.sum_eq_sum_iff_of_le (f := fun _ => 1) (g := k)
          (s := Finset.univ) (fun j hj => hge j hj)).mp (by rw [hs]; simp)
        funext j
        exact (heq j (Finset.mem_univ _)).symm
      obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
    · intro h
      exfalso; apply h
      simp [Finset.mem_piAntidiag]
  obtain ⟨N, e⟩ : ∃ N : ℕ, Nonempty ((Fin n → Bool) ≃ Fin N) := ⟨_, ⟨Fintype.equivFin _⟩⟩
  obtain ⟨e⟩ := e
  have hC : (2:ℝ)^n * (n.factorial : ℝ) ≠ 0 := by positivity
  refine ⟨N, fun i => ((∏ j, (if e.symm i j then 1 else -1 : ℚ)) / (2^n * n.factorial : ℚ)),
    fun i j => if h : (i:ℕ) < N then sg (e.symm ⟨i, h⟩ j) else 0, ?_, ?_⟩
  · rw [havals]
    intro i j
    rw [dif_pos i.isLt]
    simp only [hsg]
    split_ifs <;> norm_num
  · have ha : ∀ (i : Fin N) (j : Fin n), (if h : (i:ℕ) < N then sg (e.symm ⟨i, h⟩ j) else 0)
        = sg (e.symm i j) := by
      intro i j
      rw [dif_pos i.isLt]
    have hc : ∀ i : Fin N, (((∏ j, (if e.symm i j then 1 else -1 : ℚ)) / (2^n * n.factorial : ℚ) : ℚ) : ℝ)
        = (∏ j, sg (e.symm i j)) / ((2:ℝ)^n * (n.factorial : ℝ)) := by
      intro i
      rw [hsg]
      push_cast
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      split_ifs <;> norm_num
    simp only [ha, hc]
    have hsum := Equiv.sum_comp e.symm (fun s : Fin n → Bool =>
      (∏ j, sg (s j)) / ((2:ℝ)^n * (n.factorial : ℝ)) * (∑ j, sg (s j) * x j) ^ n)
    rw [hsum]
    have hdiv : ∀ s : Fin n → Bool, (∏ j, sg (s j)) / ((2:ℝ)^n * (n.factorial : ℝ)) * (∑ j, sg (s j) * x j) ^ n
        = (∏ j, sg (s j)) * (∑ j, sg (s j) * x j) ^ n / ((2:ℝ)^n * (n.factorial : ℝ)) :=
      fun s => by ring
    simp_rw [hdiv]
    rw [← Finset.sum_div, key]
    field_simp
