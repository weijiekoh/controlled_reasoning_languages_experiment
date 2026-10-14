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
  obtain ⟨sgn, hsgn⟩ : ∃ s : Bool → ℝ, ∀ b, s b = if b then 1 else -1 := ⟨_, fun _ => rfl⟩
  have hA : ∀ (m : ℕ) (g : Fin m → ℝ), (∑ j, g j) ^ m = ∑ q : Fin m → Fin m, ∏ k, g (q k) := by
    intro m g
    have h1 : (∑ j, g j) ^ m = ∏ _k : Fin m, ∑ j, g j := by simp
    rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hB : ∀ q : Fin n → Fin n, ∑ f : Fin n → Bool, (∏ j, sgn (f j)) * (∏ k, sgn (f (q k)))
      = if Function.Bijective q then (2:ℝ)^n else 0 := by
    intro q
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℕ, ∀ j, c j = (Finset.univ.filter (fun k => q k = j)).card :=
      ⟨_, fun j => rfl⟩
    have h1 : ∀ f : Fin n → Bool, (∏ j, sgn (f j)) * (∏ k, sgn (f (q k)))
        = ∏ j, sgn (f j) ^ (c j + 1) := by
      intro f
      have h2 : ∏ k, sgn (f (q k)) = ∏ j, sgn (f j) ^ (c j) := by
        rw [← Finset.prod_fiberwise Finset.univ q]
        apply Finset.prod_congr rfl
        intro j _
        rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2])]
        rw [Finset.prod_const, hc]
      rw [h2, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      rw [pow_succ]; ring
    simp only [h1]
    have hfp := Fintype.prod_sum (fun (j : Fin n) (b : Bool) => sgn b ^ (c j + 1))
    rw [← hfp]
    by_cases hb : Function.Bijective q
    · rw [if_pos hb]
      have hc1 : ∀ j, c j = 1 := by
        intro j
        obtain ⟨k0, hk0⟩ := hb.2 j
        rw [hc, Finset.card_eq_one]
        refine ⟨k0, ?_⟩
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => hb.1 (h.trans hk0.symm), fun h => h ▸ hk0⟩
      simp [hc1, Fintype.sum_bool, hsgn]
    · rw [if_neg hb]
      have hz : ∃ j, c j = 0 := by
        by_contra hne
        push_neg at hne
        apply hb
        have hsurj : Function.Surjective q := by
          intro j
          have hpos : (Finset.univ.filter (fun k => q k = j)).Nonempty := by
            apply Finset.card_pos.mp
            rw [← hc]
            exact Nat.pos_of_ne_zero (hne j)
          obtain ⟨k, hk⟩ := hpos
          exact ⟨k, (Finset.mem_filter.mp hk).2⟩
        exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
      obtain ⟨j0, hj0⟩ := hz
      apply Finset.prod_eq_zero (Finset.mem_univ j0)
      simp [hj0, Fintype.sum_bool, hsgn]
  have hperm : ∑ q ∈ (Finset.univ : Finset (Fin n → Fin n)).filter Function.Bijective, ∏ k, x (q k)
      = (n.factorial : ℝ) * ∏ k, x k := by
    have h1 : ∑ σ : Equiv.Perm (Fin n), ∏ k, x (σ k)
        = ∑ q ∈ (Finset.univ : Finset (Fin n → Fin n)).filter Function.Bijective, ∏ k, x (q k) := by
      refine Finset.sum_bij (fun σ _ => (σ : Fin n → Fin n)) ?_ ?_ ?_ ?_
      · intro σ _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact σ.bijective
      · intro a _ b _ h; exact Equiv.ext (fun k => congrFun h k)
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨Equiv.ofBijective q hq, Finset.mem_univ _, rfl⟩
      · intro σ _; rfl
    rw [← h1]
    simp only [Equiv.prod_comp, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul]
  have hCL : ∑ f : Fin n → Bool, (∏ j, sgn (f j)) * (∑ j, sgn (f j) * x j) ^ n
      = (2:ℝ)^n * (n.factorial : ℝ) * ∏ j, x j := by
    have step1 : ∀ f : Fin n → Bool, (∑ j, sgn (f j) * x j) ^ n
        = ∑ q : Fin n → Fin n, (∏ k, sgn (f (q k))) * ∏ k, x (q k) := by
      intro f
      rw [hA]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.prod_mul_distrib]
    have step2 : ∑ f : Fin n → Bool, (∏ j, sgn (f j)) * (∑ j, sgn (f j) * x j) ^ n
        = ∑ q : Fin n → Fin n, (∑ f : Fin n → Bool, (∏ j, sgn (f j)) * (∏ k, sgn (f (q k))))
            * ∏ k, x (q k) := by
      simp only [step1, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro f _
      ring
    rw [step2]
    simp only [hB, ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.mul_sum, hperm]
    ring
  set N := Fintype.card (Fin n → Bool) with hN
  have hNeq : (N : ℕ) = 2 ^ n := by simp [hN, Fintype.card_fun]
  let e : (Fin n → Bool) ≃ Fin N := Fintype.equivFin (Fin n → Bool)
  refine ⟨N, fun k => (∏ j, (if e.symm k j then (1:ℚ) else -1)) / (2^n * (n.factorial : ℚ)),
    fun i => if h : i < N then (fun j => sgn (e.symm ⟨i, h⟩ j)) else 0, ?_, ?_⟩
  · rw [havals]
    intro i j
    have hi : (i : ℕ) < N := i.isLt
    simp only [dif_pos hi]
    rw [hsgn]
    split_ifs <;> norm_num
  · have hcast : ∀ k : Fin N, (((∏ j, (if e.symm k j then (1:ℚ) else -1)) / (2^n * (n.factorial : ℚ)) : ℚ) : ℝ)
        = (∏ j, sgn (e.symm k j)) / ((2:ℝ)^n * (n.factorial : ℝ)) := by
      intro k
      simp only [hsgn]
      rw [Rat.cast_div, Rat.cast_prod]
      push_cast
      congr 1
      apply Finset.prod_congr rfl; intro j _
      split_ifs <;> norm_num
    have hsum : ∑ k : Fin N, (∏ j, sgn (e.symm k j)) * (∑ j, sgn (e.symm k j) * x j) ^ n
        = ∑ f : Fin n → Bool, (∏ j, sgn (f j)) * (∑ j, sgn (f j) * x j) ^ n :=
      Equiv.sum_comp e.symm (fun f : Fin n → Bool => (∏ j, sgn (f j)) * (∑ j, sgn (f j) * x j) ^ n)
    have hf : ∑ k : Fin N, (∏ j, sgn (e.symm k j)) / ((2:ℝ)^n * (n.factorial : ℝ)) * (∑ j, sgn (e.symm k j) * x j) ^ n
        = ∏ j, x j := by
      have h3 : ∑ k : Fin N, (∏ j, sgn (e.symm k j)) / ((2:ℝ)^n * (n.factorial : ℝ)) * (∑ j, sgn (e.symm k j) * x j) ^ n
          = (1 / ((2:ℝ)^n * (n.factorial : ℝ))) * ∑ k : Fin N, (∏ j, sgn (e.symm k j)) * (∑ j, sgn (e.symm k j) * x j) ^ n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [h3, hsum, hCL]
      have hf0 : (2:ℝ)^n * (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    simp only [Fin.is_lt, dite_true, Fin.eta]
    simp only [hcast]
    rw [hf]
