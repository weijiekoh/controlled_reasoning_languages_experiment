  have W : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) (g : Fin k → ι) (hg : Function.Surjective g),
      (Finset.univ.filter (fun b : Fin k → Bool => ∀ i, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))).card * 2^(Fintype.card ι) = 2^k := by
    intro ι _ _ k g hg
    classical
    let par : (Fin k → Bool) → ι → Bool := fun b i => decide (Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))
    have h1 : 2^k = ∑ t : ι → Bool, (Finset.univ.filter (fun b => par b = t)).card := by
      have := Finset.card_eq_sum_card_fiberwise (f := par) (s := (Finset.univ : Finset (Fin k → Bool))) (t := (Finset.univ : Finset (ι → Bool))) (fun _ _ => Finset.mem_univ _)
      simpa using this
    let p : ι → Fin k := Function.surjInv hg
    have hp : ∀ i, g (p i) = i := fun i => Function.surjInv_eq hg i
    have key : ∀ (t : ι → Bool) (b : Fin k → Bool) (i : ι),
        par (fun j => xor (b j) (decide (p (g j) = j) && t (g j))) i = xor (par b i) (t i) := by
      intro t b i
      have hE : (∑ j, if g j = i ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = if t i = true then 1 else 0 := by
        have : ∀ j, (if g j = i ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = if j = p i then (if t i = true then 1 else 0) else 0 := by
          intro j
          by_cases hj : j = p i
          · subst hj
            simp [hp]
          · have : ¬ (g j = i ∧ (decide (p (g j) = j) && t (g j)) = true) := by
              rintro ⟨h1, h2⟩
              simp at h2
              apply hj
              rw [← h1]; exact h2.1.symm
            rw [if_neg this, if_neg hj]
        rw [Finset.sum_congr rfl (fun j _ => this j)]
        simp
      have hsum : (∑ j, if g j = i ∧ (xor (b j) (decide (p (g j) = j) && t (g j))) = true then 1 else 0)
          + 2 * (∑ j, if g j = i ∧ b j = true ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0)
          = (∑ j, if g j = i ∧ b j = true then 1 else 0) + (∑ j, if g j = i ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        cases hb : b j <;> cases he : (decide (p (g j) = j) && t (g j)) <;> by_cases hgi : g j = i <;> simp [hb, he, hgi]
      rw [hE] at hsum
      simp only [par]
      by_cases ht : t i = true
      · rw [if_pos ht] at hsum
        simp only [ht]
        generalize (∑ j, if g j = i ∧ (xor (b j) (decide (p (g j) = j) && t (g j))) = true then 1 else 0) = a' at hsum ⊢
        generalize (∑ j, if g j = i ∧ b j = true then 1 else 0) = a at hsum ⊢
        generalize (∑ j, if g j = i ∧ b j = true ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = X at hsum
        simp only [Nat.odd_iff]
        by_cases h : a % 2 = 1 <;> by_cases h' : a' % 2 = 1 <;> simp [h, h'] <;> omega
      · rw [if_neg ht] at hsum
        have : t i = false := by simpa using ht
        simp only [this]
        generalize (∑ j, if g j = i ∧ (xor (b j) (decide (p (g j) = j) && t (g j))) = true then 1 else 0) = a' at hsum ⊢
        generalize (∑ j, if g j = i ∧ b j = true then 1 else 0) = a at hsum ⊢
        generalize (∑ j, if g j = i ∧ b j = true ∧ (decide (p (g j) = j) && t (g j)) = true then 1 else 0) = X at hsum
        simp only [Nat.odd_iff]
        by_cases h : a % 2 = 1 <;> by_cases h' : a' % 2 = 1 <;> simp [h, h'] <;> omega
    have h2 : ∀ t : ι → Bool, (Finset.univ.filter (fun b => par b = t)).card = (Finset.univ.filter (fun b => par b = fun _ => false)).card := by
      intro t
      apply Finset.card_nbij' (fun b j => xor (b j) (decide (p (g j) = j) && t (g j))) (fun b j => xor (b j) (decide (p (g j) = j) && t (g j)))
      · intro b hb
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
        funext i
        rw [key, congrFun hb i]
        cases t i <;> rfl
      · intro b hb
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
        funext i
        rw [key, congrFun hb i]
        cases t i <;> rfl
      · intro b _
        funext j
        show (xor (xor (b j) (decide (p (g j) = j) && t (g j))) (decide (p (g j) = j) && t (g j))) = b j
        generalize b j = x
        generalize (decide (p (g j) = j) && t (g j)) = y
        cases x <;> cases y <;> rfl
      · intro b _
        funext j
        show (xor (xor (b j) (decide (p (g j) = j) && t (g j))) (decide (p (g j) = j) && t (g j))) = b j
        generalize b j = x
        generalize (decide (p (g j) = j) && t (g j)) = y
        cases x <;> cases y <;> rfl
    have h3 : (Finset.univ.filter (fun b : Fin k → Bool => ∀ i, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))) = Finset.univ.filter (fun b => par b = fun _ => false) := by
      ext b
      simp [par, funext_iff]
    rw [h3]
    rw [h1, Finset.sum_congr rfl (fun t _ => h2 t)]
    simp [mul_comm]
