  have A : ∀ (n:ℕ+), ∀ (k:ℕ) (f : Fin k → Fin (2*n)), lamps_final_state n (List.ofFn f) = List.ofFn (fun i : Fin (2*n) => decide (Odd (∑ j, if f j = i then 1 else 0))) := by
    intro n k
    induction k with
    | zero => intro f; simp [lamps_final_state]
    | succ k ih =>
      intro f
      rw [List.ofFn_succ]
      simp only [lamps_final_state]
      rw [ih]
      apply List.ext_getElem
      · simp [switch_lamp]
      · intro i h1 h2
        simp only [switch_lamp, List.getElem_mapIdx, List.getElem_ofFn]
        rw [Fin.sum_univ_succ]
        generalize (∑ j : Fin k, if f j.succ = (⟨i, by simpa using h2⟩ : Fin (2*n)) then 1 else 0) = s
        by_cases h : f 0 = ⟨i, by simpa using h2⟩
        · have h' : i = ((f 0 : Fin (2*n)) : ℕ) := by rw [h]
          rw [if_pos h', if_pos h]
          cases hs : Nat.even_or_odd s with
          | inl he => simp [Nat.odd_add, he, Nat.not_odd_iff_even.mpr he]
          | inr ho => simp [Nat.odd_add, ho, Nat.not_even_iff_odd.mpr ho]
        · have h' : ¬ i = ((f 0 : Fin (2*n)) : ℕ) := fun e => h (Fin.ext e.symm)
          rw [if_neg h', if_neg h]
          simp
