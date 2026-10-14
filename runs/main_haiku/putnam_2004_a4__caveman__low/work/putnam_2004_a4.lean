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
  let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) := finFunctionFinEquiv
  let sv : Fin 2 → ℝ := fun b => if b = 0 then 1 else -1
  let sR : (Fin n → Fin 2) → Fin n → ℝ := fun f j => sv (f j)
  let sQ : (Fin n → Fin 2) → Fin n → ℚ := fun f j => if f j = 0 then 1 else -1
  let cQ : (Fin n → Fin 2) → ℚ := fun f => (∏ j, sQ f j) / (2 ^ n * (n.factorial : ℚ))
  have hsq : ∀ f j, ((sQ f j : ℚ) : ℝ) = sR f j := by
    intro f j
    simp only [sQ, sR, sv]
    split_ifs <;> norm_num
  have hpow : ∀ (m : ℕ) (y : ℝ), (∑ b : Fin 2, sv b ^ m * y) = (1 + (-1) ^ m) * y := by
    intro m y
    simp [Fin.sum_univ_two, sv]; ring
  have expand : ∀ f : Fin n → Fin 2,
      (∏ j, sR f j) * (∑ j, sR f j * x j) ^ n =
      ∑ k ∈ Finset.univ.piAntidiag n,
        (Nat.multinomial Finset.univ k : ℝ) * ∏ j, sR f j ^ (k j + 1) * x j ^ (k j) := by
    intro f
    rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hk : ∏ j, sR f j ^ (k j + 1) * x j ^ (k j) = (∏ j, sR f j) * ∏ j, (sR f j * x j) ^ (k j) := by
      rw [← Finset.prod_mul_distrib]; congr 1; funext j; ring
    rw [hk]; ring
  have colsum : ∀ k : Fin n → ℕ, ∑ f : Fin n → Fin 2, ∏ j, sR f j ^ (k j + 1) * x j ^ (k j)
      = ∏ j, (1 + (-1) ^ (k j + 1)) * x j ^ (k j) := by
    intro k
    have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
      (fun j b => sv b ^ (k j + 1) * x j ^ (k j))
    simp only [Fintype.piFinset_univ] at h
    calc ∑ f : Fin n → Fin 2, ∏ j, sR f j ^ (k j + 1) * x j ^ (k j)
        = ∏ j, ∑ b : Fin 2, sv b ^ (k j + 1) * x j ^ (k j) := h.symm
      _ = ∏ j, (1 + (-1) ^ (k j + 1)) * x j ^ (k j) :=
          Finset.prod_congr rfl (fun j _ => hpow _ _)
  have main : ∑ f : Fin n → Fin 2, (∏ j, sR f j) * (∑ j, sR f j * x j) ^ n
      = 2 ^ n * (n.factorial : ℝ) * ∏ j, x j := by
    rw [Finset.sum_congr rfl (fun f _ => expand f), Finset.sum_comm]
    have hk : ∀ k ∈ Finset.univ.piAntidiag n,
        ∑ f : Fin n → Fin 2, (Nat.multinomial Finset.univ k : ℝ) * ∏ j, sR f j ^ (k j + 1) * x j ^ (k j)
        = (Nat.multinomial Finset.univ k : ℝ) * ∏ j, (1 + (-1) ^ (k j + 1)) * x j ^ (k j) := by
      intro k _
      rw [← Finset.mul_sum, colsum k]
    rw [Finset.sum_congr rfl hk]
    rw [Finset.sum_eq_single (fun _ => 1)]
    · simp [Nat.multinomial, Finset.prod_mul_distrib]
      norm_num
      ring
    · intro k hkmem hne
      by_cases h : ∃ j, Even (k j)
      · obtain ⟨j, hj⟩ := h
        have hz : (1 + (-1 : ℝ) ^ (k j + 1)) * x j ^ (k j) = 0 := by
          rw [hj.add_one.neg_one_pow]; norm_num
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]
      · push Not at h
        have hpos : ∀ j, 1 ≤ k j := fun j => (Nat.not_even_iff_odd.mp (h j)).pos
        have hsum : ∑ j, k j = n := (Finset.mem_piAntidiag.mp hkmem).1
        have heq : ∑ _j : Fin n, (1 : ℕ) = ∑ j, k j := by simp [hsum]
        have hall := (Finset.sum_eq_sum_iff_of_le (fun j _ => hpos j)).mp heq
        exact absurd (funext fun j => (hall j (Finset.mem_univ j)).symm) hne
    · intro hnot
      exact absurd (Finset.mem_piAntidiag.mpr ⟨by simp, by simp⟩) hnot
  refine ⟨2 ^ n, fun i => cQ (e.symm i),
    fun i j => if h : (i : ℕ) < 2 ^ n then sR (e.symm ⟨i, h⟩) j else 0, ?_, ?_⟩
  · rw [havals]
    intro i j
    rw [dif_pos i.isLt]
    simp only [sR, sv]
    split_ifs <;> norm_num
  · have hA : ∀ (i : Fin (2 ^ n)) (j : Fin n),
        (if h : (i : ℕ) < 2 ^ n then sR (e.symm ⟨i, h⟩) j else 0) = sR (e.symm i) j := by
      intro i j
      rw [dif_pos i.isLt]
    simp only [hA]
    have hs := Equiv.sum_comp e.symm (fun f => ((cQ f : ℚ) : ℝ) * (∑ j, sR f j * x j) ^ n)
    rw [hs]
    have hc : ∀ f : Fin n → Fin 2, ((cQ f : ℚ) : ℝ) * (∑ j, sR f j * x j) ^ n
        = (1 / (2 ^ n * (n.factorial : ℝ))) * ((∏ j, sR f j) * (∑ j, sR f j * x j) ^ n) := by
      intro f
      simp only [cQ]
      push_cast
      simp only [hsq]
      ring
    rw [Finset.sum_congr rfl (fun f _ => hc f), ← Finset.mul_sum, main]
    have hne : (2 ^ n * (n.factorial : ℝ)) ≠ 0 := by
      have := Nat.factorial_pos n
      positivity
    field_simp
