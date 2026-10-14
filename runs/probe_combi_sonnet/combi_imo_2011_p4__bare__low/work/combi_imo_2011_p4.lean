import Mathlib

def weight_of_left_pan {n : ℕ} (σ : Equiv.Perm (Fin n)) (place_left : Fin n → Bool) (step : ℕ) : ℕ :=
  ∑ j with place_left j = true ∧ σ j ≤ step, 2 ^ j.1

def weight_of_right_pan {n : ℕ} (σ : Equiv.Perm (Fin n)) (place_left : Fin n → Bool) (step : ℕ) : ℕ :=
  ∑ j with place_left j = false ∧ σ j ≤ step, 2 ^ j.1

def is_valid_placement {n : ℕ} (σ : Equiv.Perm (Fin n)) (place_left : Fin n → Bool) : Prop :=
  ∀ step : Fin n, weight_of_right_pan σ place_left step ≤ weight_of_left_pan σ place_left step

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (place_left : Fin n → Bool) :
  Decidable (is_valid_placement σ place_left) := by
  simp [is_valid_placement]; infer_instance

abbrev all_placements (n : ℕ) :=
  Finset.product (@Finset.univ (Equiv.Perm (Fin n)) _) (@Finset.univ (Fin n → Bool) _)

abbrev valid_placements (n : ℕ) :=
  all_placements n |>.filter (fun (σ, f) => is_valid_placement σ f)

noncomputable abbrev imo_2011_p4_solution : ℕ → ℕ := fun n => Nat.doubleFactorial (2 * n - 1)

/--
Let $n > 0$ be an integer. We are given a balance and $n$ weights of weight $2^0,2^1, \cdots ,2^{n-1}$. We are to place each of the $n$ weights on the balance, one after another, in such a way that the right pan is never heavier than the left pan. At each step we choose one of the weights that has not yet been placed on the balance, and place it on either the left pan or the right pan, until all of the weights have been placed. Determine the number of ways in which this can be done.
-/
theorem imo_2011_p4 (n : ℕ) (hn : n > 0) :
    (valid_placements n).card = imo_2011_p4_solution n := by
  clear hn
  obtain ⟨D, hD⟩ : ∃ D : (m : ℕ) → Equiv.Perm (Fin m) → (Fin m → Bool) → ℕ → ℤ,
      ∀ m σ f s, D m σ f s = ∑ j : Fin m, (if (σ j : ℕ) < s then (if f j = true then (1:ℤ) else -1) else 0) * 2 ^ (j : ℕ) :=
    ⟨fun m σ f s => ∑ j : Fin m, (if (σ j : ℕ) < s then (if f j = true then (1:ℤ) else -1) else 0) * 2 ^ (j : ℕ), fun _ _ _ _ => rfl⟩
  have hD0 : ∀ m σ f, D m σ f 0 = 0 := by intros; simp [hD]
  obtain ⟨ins, hins0, hinss⟩ : ∃ ins : (m : ℕ) → Fin (m+1) → Equiv.Perm (Fin m) → Equiv.Perm (Fin (m+1)),
      (∀ m p τ, ins m p τ 0 = p) ∧ ∀ m p τ j, ins m p τ j.succ = p.succAbove (τ j) := by
    refine ⟨fun m p τ => (Fin.cycleRange p).symm * Equiv.Perm.decomposeFin.symm (0, τ), ?_, ?_⟩
    · intro m p τ
      simp [Equiv.Perm.decomposeFin_symm_apply_zero]
    · intro m p τ j
      simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]
  have Z : ∀ m (ε : Fin m → ℤ), (∀ j, ε j = 0 ∨ ε j = 1 ∨ ε j = -1) → (∃ j, ε j ≠ 0) →
      ∑ j : Fin m, ε j * 2 ^ (j:ℕ) ≠ 0 := by
    intro m
    induction m with
    | zero => intro ε _ ⟨j, _⟩; exact j.elim0
    | succ m ih =>
      intro ε hε ⟨j, hj⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have e : ∑ k : Fin m, ε k.succ * 2 ^ ((k:ℕ)+1) = 2 * ∑ k : Fin m, ε k.succ * 2 ^ (k:ℕ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [e]
      by_cases h0 : ε 0 = 0
      · have h3 : ∃ k : Fin m, ε k.succ ≠ 0 := by
          cases j using Fin.cases with
          | zero => exact absurd h0 hj
          | succ k => exact ⟨k, hj⟩
        have := ih (fun k : Fin m => ε k.succ) (fun k => hε k.succ) h3
        intro h; apply this; omega
      · intro h; rcases hε 0 with h1|h1|h1 <;> omega
  have hvalid : ∀ m (σ : Equiv.Perm (Fin m)) f, is_valid_placement σ f ↔ ∀ s, s ≤ m → 0 ≤ D m σ f s := by
    intro m σ f
    have key : ∀ s : ℕ, D m σ f (s+1) = (weight_of_left_pan σ f s : ℤ) - weight_of_right_pan σ f s := by
      intro s
      rw [hD, weight_of_left_pan, weight_of_right_pan, Finset.sum_filter, Finset.sum_filter]
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hf : f j = true <;> by_cases hs : (σ j:ℕ) ≤ s <;> simp [hf, hs, Nat.lt_succ_iff]
    constructor
    · intro h s hs
      cases s with
      | zero => simp [hD0]
      | succ s =>
        rw [key]
        have h2 : (weight_of_right_pan σ f s : ℤ) ≤ weight_of_left_pan σ f s := by
          exact_mod_cast h ⟨s, by omega⟩
        linarith
    · intro h s
      have := h (s+1) (by have := s.2; omega)
      rw [key] at this
      have h3 : (weight_of_right_pan σ f s : ℤ) ≤ weight_of_left_pan σ f s := by linarith
      exact_mod_cast h3
  have hcoe : ∀ m (p : Fin (m+1)) (x : Fin m), (p.succAbove x : ℕ) = if (x:ℕ) < p then (x:ℕ) else (x:ℕ)+1 := by
    intro m p x
    rcases lt_or_ge (x:ℕ) p with h|h
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp [h]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]; simp [not_lt.2 h]
  have hsucc : ∀ m (p : Fin (m+1)) (τ : Equiv.Perm (Fin m)) (b : Bool) (f' : Fin m → Bool) (s : ℕ),
      D (m+1) (ins m p τ) (Fin.cons b f' : Fin (m+1) → Bool) s =
        (if (p:ℕ) < s then (if b = true then (1:ℤ) else -1) else 0) +
          2 * D m τ f' (if s ≤ (p:ℕ) then s else s - 1) := by
    intro m p τ b f' s
    rw [hD (m+1), Fin.sum_univ_succ, hD m, Finset.mul_sum]
    simp only [hins0, hinss, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hcoe]
    split_ifs <;> first | omega | ring
  have hnz : ∀ m (τ : Equiv.Perm (Fin m)) f' t, 1 ≤ t → 0 < m → D m τ f' t ≠ 0 := by
    intro m τ f' t ht hm
    rw [hD]
    refine Z m (fun j => if (τ j:ℕ) < t then (if f' j = true then (1:ℤ) else -1) else 0) ?_ ?_
    · intro j; by_cases h : (τ j : ℕ) < t <;> by_cases h2 : f' j = true <;> simp [h, h2]
    · exact ⟨τ.symm ⟨0, hm⟩, by simp <;> omega⟩
  have hins_inj : ∀ m (p p' : Fin (m+1)) (τ τ' : Equiv.Perm (Fin m)), ins m p τ = ins m p' τ' → p = p' ∧ τ = τ' := by
    intro m p p' τ τ' h
    have hpp : p = p' := by
      have := congrArg (fun g => g 0) h
      simpa [hins0] using this
    subst hpp
    refine ⟨rfl, ?_⟩
    ext j
    have := congrArg (fun g => g j.succ) h
    simp only [hinss] at this
    exact congrArg Fin.val (Fin.succAbove_right_inj.1 this)
  have hins_surj : ∀ m (σ : Equiv.Perm (Fin (m+1))), ∃ p τ, ins m p τ = σ := by
    intro m
    have hb := (Fintype.bijective_iff_injective_and_card (fun q : Fin (m+1) × Equiv.Perm (Fin m) => ins m q.1 q.2)).2
      ⟨fun a b h => by
        obtain ⟨h1, h2⟩ := hins_inj _ _ _ _ _ h
        exact Prod.ext h1 h2,
       by simp [Fintype.card_perm, Nat.factorial_succ]⟩
    intro σ
    obtain ⟨⟨p, τ⟩, h⟩ := hb.2 σ
    exact ⟨p, τ, h⟩
  have step : ∀ m, (valid_placements (m+1)).card = (2*m+1) * (valid_placements m).card := by
    intro m
    have hQ : (Finset.univ.filter (fun q : Fin (m+1) × Bool => q.2 = true ∨ q.1 ≠ 0)).card = 2*m+1 := by
      have : (Finset.univ.filter (fun q : Fin (m+1) × Bool => q.2 = true ∨ q.1 ≠ 0)) = Finset.univ.erase ((0:Fin (m+1)), false) := by
        ext ⟨a, b⟩; cases b <;> simp
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_prod]
      simp; omega
    have hc : ((valid_placements m) ×ˢ (Finset.univ.filter (fun q : Fin (m+1) × Bool => q.2 = true ∨ q.1 ≠ 0))).card
        = (valid_placements (m+1)).card := by
      apply Finset.card_bij (fun (a : (Equiv.Perm (Fin m) × (Fin m → Bool)) × (Fin (m+1) × Bool)) _ =>
        (ins m a.2.1 a.1.1, (Fin.cons a.2.2 a.1.2 : Fin (m+1) → Bool)))
      · rintro ⟨⟨τ, f'⟩, ⟨p, b⟩⟩ ha
        simp only [valid_placements, all_placements, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at ha ⊢
        obtain ⟨hv, hq⟩ := ha
        rw [hvalid] at hv ⊢
        intro s hs
        rw [hsucc]
        have hp := p.2
        by_cases h1 : s ≤ (p:ℕ)
        · rw [if_pos h1, if_neg (by omega)]
          have := hv s (by omega)
          omega
        · rw [if_neg h1, if_pos (by omega)]
          have := hv (s-1) (by omega)
          by_cases hb : b = true
          · rw [if_pos hb]; omega
          · rw [if_neg hb]
            have hp0 : (p:ℕ) ≠ 0 := by
              rcases hq with h|h
              · exact absurd h hb
              · intro h'; exact h (Fin.ext h')
            have hne := hnz m τ f' (s-1) (by omega) (by omega)
            omega
      · rintro ⟨⟨τ, f'⟩, ⟨p, b⟩⟩ _ ⟨⟨τ', f''⟩, ⟨p', b'⟩⟩ _ h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨rfl, rfl⟩ := hins_inj _ _ _ _ _ h1
        obtain ⟨rfl, rfl⟩ := Fin.cons_injective2 h2
        rfl
      · rintro ⟨σ, f⟩ hb
        obtain ⟨p, τ, rfl⟩ := hins_surj m σ
        obtain ⟨b, f', rfl⟩ : ∃ b f', f = (Fin.cons b f' : Fin (m+1) → Bool) :=
          ⟨f 0, Fin.tail f, (Fin.cons_self_tail f).symm⟩
        refine ⟨⟨(τ, f'), (p, b)⟩, ?_, rfl⟩
        simp only [valid_placements, all_placements, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hb ⊢
        rw [hvalid] at hb
        refine ⟨?_, ?_⟩
        · rw [hvalid]; intro s hs
          have hp := p.2
          by_cases h1 : s ≤ (p:ℕ)
          · have := hb s (by omega)
            rw [hsucc, if_pos h1, if_neg (show ¬ ((p:ℕ) < s) by omega)] at this
            omega
          · have := hb (s+1) (by omega)
            rw [hsucc, if_pos (show (p:ℕ) < s+1 by omega), if_neg (show ¬ (s+1 ≤ (p:ℕ)) by omega), Nat.add_sub_cancel] at this
            by_cases hb' : b = true
            · rw [if_pos hb'] at this; omega
            · rw [if_neg hb'] at this; omega
        · by_contra hc
          push Not at hc
          obtain ⟨hb1, hp0⟩ := hc
          have hp0' : (p:ℕ) = 0 := by rw [hp0]; rfl
          have h := hb 1 (by omega)
          rw [hsucc, if_pos (by omega), if_neg hb1, if_neg (by omega), Nat.sub_self, hD0] at h
          omega
    rw [Finset.card_product, hQ] at hc
    rw [← hc]; ring
  induction n with
  | zero =>
    have h0 : imo_2011_p4_solution 0 = 1 := by simp [imo_2011_p4_solution]
    rw [h0, Finset.card_eq_one]
    refine ⟨(1, fun x => x.elim0), ?_⟩
    ext ⟨σ, f⟩
    simp only [valid_placements, all_placements, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    have h1 : σ = 1 := Subsingleton.elim _ _
    have h2 : f = fun x => x.elim0 := Subsingleton.elim _ _
    subst h1 h2
    simp [is_valid_placement]
  | succ m ih =>
    rw [step, ih]
    have : 2*(m+1)-1 = (2*m)+1 := by omega
    simp only [imo_2011_p4_solution, this, Nat.doubleFactorial_add_one]
