  have mainN : ∀ (n k : ℕ+) (hk : (n:ℕ) ≤ k) (hex : ∃ g : Fin k → Fin n, ∀ i : Fin n, Odd (∑ j, if g j = i then 1 else 0)),
      N n k = 2^((k:ℕ)-n) * M n k ∧ 0 < M n k := by
    intro n k hk hex
    classical
    have hn := n.pos
    have h2n : (n:ℕ) ≤ 2 * n := by omega
    let G : Finset (Fin k → Fin n) := Finset.univ.filter (fun g => ∀ i : Fin n, Odd (∑ j, if g j = i then 1 else 0))
    let Bs : (Fin k → Fin n) → Finset (Fin k → Bool) := fun g =>
      Finset.univ.filter (fun b : Fin k → Bool => ∀ i : Fin n, ¬ Odd (∑ j, if g j = i ∧ b j = true then 1 else 0))
    have hN1 : N n k = (Finset.univ.filter (fun f : Fin k → Fin (2*n) => ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n)).card := by
      unfold N
      congr 1
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Bc n k f
    have hM1 : M n k = (Finset.univ.filter (fun f : Fin k → Fin (2*n) => (∀ j, (f j).val < n) ∧ ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n)).card := by
      unfold M
      congr 1
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Bc n k f]
      exact Iff.rfl
    have hMG : M n k = G.card := by
      rw [hM1]
      symm
      apply Finset.card_bij (fun g _ => fun j => Fin.castLE h2n (g j))
      · intro g hg
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun j => (g j).isLt, fun i => ?_⟩
        rw [Cc]
        by_cases h : i.val < n
        · rw [dif_pos h]; simpa [h] using hg ⟨i, h⟩
        · rw [dif_neg h]; simp [h]
      · intro g _ g' _ e
        funext j
        exact Fin.castLE_injective h2n (congrFun e j)
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨hlt, hodd⟩ := hf
        refine ⟨fun j => ⟨(f j).val, hlt j⟩, ?_, ?_⟩
        · simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
          intro i
          have := (hodd (Fin.castLE h2n i)).2 (by simp)
          have e : (∑ x, if (⟨(f x).val, hlt x⟩ : Fin n) = i then 1 else 0) = ∑ j, if f j = Fin.castLE h2n i then 1 else 0 :=
            Finset.sum_congr rfl (fun j _ => if_congr (by rw [Fin.ext_iff, Fin.ext_iff]; simp [eq_comm]) rfl rfl)
          rw [e]; exact this
        · funext j; exact Fin.ext rfl
    have hmod : ∀ v : ℕ, v < 2 * n → v % n = if (n:ℕ) ≤ v then v - n else v := by
      intro v hv
      split_ifs with h
      · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]
    have hcard : (Finset.univ.filter (fun f : Fin k → Fin (2*n) => ∀ i : Fin (2*n), Odd (∑ j, if f j = i then 1 else 0) ↔ i.val < n)).card = (G.sigma Bs).card := by
      refine Finset.card_nbij' (fun f => (⟨fun j => ⟨(f j).val % n, Nat.mod_lt _ hn⟩, fun j => decide ((n:ℕ) ≤ (f j).val)⟩ : Σ _ : Fin k → Fin n, Fin k → Bool))
        (fun x => fun j => ⟨(x.1 j).val + if x.2 j = true then (n:ℕ) else 0, by have := (x.1 j).isLt; split_ifs <;> omega⟩) ?_ ?_ ?_ ?_
      · intro f hf
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        have hR : ∀ j, ((f j : Fin (2*n)) : ℕ) = ((⟨(f j).val % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ) + if decide ((n:ℕ) ≤ (f j).val) = true then (n:ℕ) else 0 := by
          intro j
          have := (f j).isLt
          simp only [hmod _ this, decide_eq_true_eq]
          split_ifs <;> omega
        have := (memEq n k f _ _ hR).1 hf
        simp only [Finset.mem_coe, Finset.mem_sigma, G, Bs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact this
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_sigma, G, Bs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (memEq n k _ x.1 x.2 (fun j => rfl)).2 hx
      · intro f _
        funext j
        apply Fin.ext
        have := (f j).isLt
        simp only [hmod _ this, decide_eq_true_eq]
        split_ifs <;> omega
      · rintro ⟨g, b⟩ _
        refine Sigma.ext ?_ (heq_of_eq ?_)
        · funext j
          apply Fin.ext
          have := (g j).isLt
          show ((g j).val + if b j = true then (n:ℕ) else 0) % n = (g j).val
          split_ifs
          · rw [Nat.add_mod_right, Nat.mod_eq_of_lt this]
          · rw [Nat.add_zero, Nat.mod_eq_of_lt this]
        · funext j
          have := (g j).isLt
          show decide ((n:ℕ) ≤ (g j).val + if b j = true then (n:ℕ) else 0) = b j
          cases hb : b j <;> simp <;> omega
    have hBs : ∀ g ∈ G, (Bs g).card = 2^((k:ℕ) - n) := by
      intro g hg
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have hsurj : Function.Surjective g := by
        intro i
        have := hg i
        by_contra hne
        push_neg at hne
        have h0 : (∑ j, if g j = i then 1 else 0) = 0 := Finset.sum_eq_zero (fun j _ => if_neg (hne j))
        rw [h0] at this
        simp at this
      have := W (ι := Fin n) k g hsurj
      simp only [Fintype.card_fin] at this
      have h3 : (2:ℕ)^(k:ℕ) = 2^((k:ℕ) - n) * 2^(n:ℕ) := by rw [← pow_add]; congr 1; omega
      rw [h3] at this
      exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0:ℕ) < 2) (n:ℕ)) (by convert this)
    refine ⟨?_, ?_⟩
    · rw [hN1, hcard, Finset.card_sigma, Finset.sum_congr rfl hBs, hMG]
      simp [mul_comm]
    · rw [hMG]
      obtain ⟨g, hg⟩ := hex
      exact Finset.card_pos.2 ⟨g, by simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]; exact hg⟩
