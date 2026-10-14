import Mathlib

open Nat


set_option maxRecDepth 100000 in
theorem izho_2019_p1 : ((@Finset.univ 100!.Partition).filter
    (fun p => ∀ i ∈ p.parts, ∃ k ∈ Finset.Icc 1 99, i = Nat.factorial k)).card ≥ 100! := by
  classical
  generalize hN : 100! = N
  obtain ⟨b, hb'⟩ : ∃ b : Fin 98 → ℕ, b = fun i => if i.val < 96 then i.val + 3 else if i.val = 96 then 297 else 98 := ⟨_, rfl⟩
  have hS : ∀ c ∈ Fintype.piFinset (fun i => Finset.range (b i)),
      ∑ i : Fin 98, c i * (i.val+2)! ≤ N := by
    intro c hc
    rw [Fintype.mem_piFinset] at hc
    calc ∑ i : Fin 98, c i * (i.val+2)! ≤ ∑ i : Fin 98, (b i - 1) * (i.val+2)! := by
          apply Finset.sum_le_sum
          intro i _
          have := Finset.mem_range.mp (hc i)
          exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ N := by rw [← hN, hb']; decide +kernel
  have hcard : (Fintype.piFinset (fun i => Finset.range (b i))).card ≥ N := by
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    rw [← hN, hb']; decide +kernel
  let f : (Fin 98 → ℕ) → Nat.Partition N := fun c =>
    if h : ∑ i : Fin 98, c i * (i.val+2)! ≤ N then
    { parts := (∑ i : Fin 98, Multiset.replicate (c i) ((i.val+2)!)) +
        Multiset.replicate (N - ∑ i : Fin 98, c i * (i.val+2)!) 1
      parts_pos := by
        intro n hn
        rw [Multiset.mem_add] at hn
        rcases hn with hn | hn
        · obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp hn
          rw [Multiset.eq_of_mem_replicate hi]; exact Nat.factorial_pos _
        · rw [Multiset.eq_of_mem_replicate hn]; exact one_pos
      parts_sum := by
        rw [Multiset.sum_add, Multiset.sum_replicate, ← Multiset.coe_sumAddMonoidHom, map_sum]
        simp only [Multiset.coe_sumAddMonoidHom, Multiset.sum_replicate, smul_eq_mul]
        omega }
    else Nat.Partition.indiscrete _
  have hfp : ∀ c : Fin 98 → ℕ, ∑ i : Fin 98, c i * (i.val+2)! ≤ N → (f c).parts =
      (∑ i : Fin 98, Multiset.replicate (c i) ((i.val+2)!)) +
        Multiset.replicate (N - ∑ i : Fin 98, c i * (i.val+2)!) 1 := by
    intro c h
    show (dite _ _ _ : Nat.Partition N).parts = _
    rw [dif_pos h]
  have hf : ∀ c ∈ Fintype.piFinset (fun i => Finset.range (b i)), ∀ j : Fin 98,
      (f c).parts.count ((j.val+2)!) = c j := by
    intro c hc j
    rw [hfp c (hS c hc)]
    rw [Multiset.count_add, Multiset.count_sum']
    have h1 : ∀ i : Fin 98, Multiset.count ((j.val+2)!) (Multiset.replicate (c i) ((i.val+2)!)) = if i = j then c i else 0 := by
      intro i
      rw [Multiset.count_replicate]
      by_cases h : i = j
      · subst h; simp
      · have : (i.val+2)! ≠ (j.val+2)! := by
          intro e
          have := Nat.factorial_inj (by omega : 1 < i.val+2) |>.mp e
          exact h (Fin.ext (by omega))
        simp [h, this.symm]
    simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Multiset.count_replicate]
    have : (1:ℕ) ≠ (j.val+2)! := by
      have := Nat.self_le_factorial (j.val+2)
      omega
    simp [this]
  refine le_trans hcard ?_
  apply Finset.card_le_card_of_injOn f
  · intro c hc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    have hc' := Finset.mem_coe.mp hc
    intro n hn
    rw [hfp c (hS c hc')] at hn
    rw [Multiset.mem_add] at hn
    rcases hn with hn | hn
    · obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp hn
      exact ⟨i.val+2, by simp; omega, Multiset.eq_of_mem_replicate hi⟩
    · exact ⟨1, by simp, by rw [Multiset.eq_of_mem_replicate hn]; rfl⟩
  · intro c hc d hd e
    funext j
    rw [← hf c (Finset.mem_coe.mp hc) j, ← hf d (Finset.mem_coe.mp hd) j, e]
