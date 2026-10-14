
lemma partA_step (n : ℕ) (s : Fin (n+1) → ℤˣ) (x : Fin (n+2))
    (ih : ∀ (s : Fin n → ℤˣ) (x : Fin (n+1)),
      (univ.filter (fun σ : Equiv.Perm (Fin (n+1)) => σ 0 = x ∧ ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val) :
    (univ.filter (fun σ : Equiv.Perm (Fin (n+2)) => σ 0 = x ∧ ∀ i : Fin (n+1), 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val := by
  rw [List.ofFn_succ]
  have hW : W (s 0 :: List.ofFn fun i => s i.succ) x.val
      = Op (s 0) (n+1) (W (List.ofFn fun i => s i.succ)) x.val := by simp [W]
  rw [hW]
  set T : Finset (Equiv.Perm (Fin (n+1))) := univ.filter (fun τ : Equiv.Perm (Fin (n+1)) =>
    (if s 0 = 1 then x.val ≤ (τ 0).val else (τ 0).val < x.val) ∧
      ∀ i : Fin n, 0 < (s i.succ : ℤ) * ((τ i.succ : ℤ) - (τ i.castSucc : ℤ))) with hT
  have h1 : T.card = (univ.filter (fun σ : Equiv.Perm (Fin (n+2)) => σ 0 = x ∧ ∀ i : Fin (n+1), 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card := by
    refine Finset.card_nbij (mkP x) ?_ ?_ ?_
    · intro τ hτ
      rw [mem_coe, hT, mem_filter] at hτ
      rw [mem_coe, mem_filter]
      exact ⟨mem_univ _, (mk_cond s x τ).2 hτ.2⟩
    · intro τ _ τ' _ h
      refine Equiv.ext (fun i => ?_)
      have := congrArg (fun σ => σ i.succ) h
      simp only [mkP_succ] at this
      exact Fin.succAbove_right_injective this
    · intro σ hσ
      rw [mem_coe, mem_filter] at hσ
      obtain ⟨hσ0, hσc⟩ := hσ.2
      have hne : ∀ i : Fin (n+1), σ i.succ ≠ x := by
        intro i h
        rw [← hσ0] at h
        exact Fin.succ_ne_zero i (σ.injective h)
      set ψ : Fin (n+2) → Fin (n+1) := Function.invFun x.succAbove with hψdef
      have hψ : ∀ i : Fin (n+1), x.succAbove (ψ (σ i.succ)) = σ i.succ := fun i =>
        Function.invFun_eq (Fin.exists_succAbove_eq (hne i))
      have inj : Function.Injective (fun i : Fin (n+1) => ψ (σ i.succ)) := by
        intro a b h
        have := hψ a
        simp only at h
        rw [h, hψ b] at this
        exact Fin.succ_injective _ (σ.injective this.symm)
      set τ : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 inj) with hτ
      have heq : mkP x τ = σ := by
        ext j
        induction j using Fin.cases with
        | zero => rw [mkP_zero, hσ0]
        | succ i => rw [mkP_succ]; exact congrArg Fin.val (hψ i)
      refine ⟨τ, ?_, heq⟩
      rw [mem_coe, hT, mem_filter]
      refine ⟨mem_univ _, (mk_cond s x τ).1 (by rw [heq]; exact ⟨hσ0, hσc⟩)⟩
  rw [← h1]
  have h2 := Finset.card_eq_sum_card_fiberwise (f := fun τ : Equiv.Perm (Fin (n+1)) => τ 0) (s := T) (t := univ) (by simp)
  rw [h2]
  have h3 : ∀ y : Fin (n+1), (T.filter (fun τ => τ 0 = y)).card =
      if (if s 0 = 1 then x.val ≤ y.val else y.val < x.val) then W (List.ofFn fun i => s i.succ) y.val else 0 := by
    intro y
    by_cases hr : (if s 0 = 1 then x.val ≤ y.val else y.val < x.val)
    · rw [if_pos hr, ← ih (fun i => s i.succ) y]
      congr 1
      ext τ
      simp only [hT, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, h⟩, h0⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩; exact ⟨⟨by rw [h0]; exact hr, h⟩, h0⟩
    · rw [if_neg hr, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro τ hτ h0
      rw [hT, mem_filter] at hτ
      rw [h0] at hτ
      exact hr hτ.2.1
  rw [sum_congr rfl (fun y _ => h3 y)]
  rw [Fin.sum_univ_eq_sum_range (fun y => if (if s 0 = 1 then x.val ≤ y else y < x.val) then W (List.ofFn fun i => s i.succ) y else 0) (n+1)]
  unfold Op
  by_cases he : s 0 = 1
  · simp only [he, if_true]
    rw [← sum_filter]
    refine sum_congr ?_ (fun _ _ => rfl)
    ext y; simp; omega
  · simp only [he, if_false]
    rw [← sum_filter]
    refine sum_congr ?_ (fun _ _ => rfl)
    ext y; simp; omega

lemma partA : ∀ (n : ℕ) (s : Fin n → ℤˣ) (x : Fin (n+1)),
    (univ.filter (fun σ : Equiv.Perm (Fin (n+1)) => σ 0 = x ∧ ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)))).card = W (List.ofFn s) x.val := by
  intro n
  induction n with
  | zero => intro s x; rw [partA_zero]; simp [W]
  | succ n ih => exact fun s x => partA_step n s x ih
