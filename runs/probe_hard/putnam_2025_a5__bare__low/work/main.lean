
theorem putnam_2025_a5
    (n : ℕ)
    (hn : 1 ≤ n)
    (s : Fin n → ℤˣ) :
    (∀ t : Fin n → ℤˣ, f n t ≤ f n s) ↔ s ∈ putnam_2025_a5_solution n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  constructor
  · intro hmax
    by_contra hns
    rcases decomp (List.ofFn s) (s 0) with ⟨pre, c, rest, h⟩ | h | ⟨b, l₁, h, hne⟩
    · have hg := flip_gt pre c rest
      have hlen : (pre ++ c :: ng (c :: rest)).length = m + 1 := by
        have := congrArg List.length h
        simp only [List.length_ofFn, List.length_append, List.length_cons, ng_length] at this ⊢
        omega
      obtain ⟨t, ht⟩ := exists_ofFn (m+1) _ hlen
      have := hmax t
      rw [f_eq, f_eq, ht, h] at this
      omega
    · apply hns
      rw [List.length_ofFn] at h
      have := alt_ofFn _ _ s h
      rcases Int.units_eq_one_or (s 0) with ha | ha
      · right
        intro i
        rw [this i, ha, one_mul]
      · left
        intro i
        rw [this i, ha, pow_succ']
    · rw [List.ofFn_succ] at h
      exact hne (List.cons.inj h).1.symm
  · intro hs t
    have hs' : FF (List.ofFn s) = FF (altL (-1) (m+1)) := by
      rcases hs with h | h
      · rw [ofFn_alt (-1) (m+1) s (fun i => by rw [h i, pow_succ']) ]
      · rw [ofFn_alt 1 (m+1) s (fun i => by rw [h i, one_mul]), FF_alt 1 (-1)]
    rw [f_eq, f_eq, hs']
    have hz := Zlem m 1 (t 0) (List.ofFn fun i : Fin m => t i.succ) le_rfl (by simp)
    have e : altL (t 0) 1 ++ List.ofFn (fun i : Fin m => t i.succ) = List.ofFn t := by
      rw [List.ofFn_succ]; rfl
    rw [e] at hz
    refine le_trans hz ?_
    rw [FF_alt (t 0) (-1), add_comm]
