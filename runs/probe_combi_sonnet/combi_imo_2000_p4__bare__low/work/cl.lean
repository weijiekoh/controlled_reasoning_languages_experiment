import Mathlib

theorem classify (F : ℕ → Fin 3)
  (H : ∀ a b c d : ℕ, 1 ≤ a → a ≤ 100 → 1 ≤ b → b ≤ 100 → 1 ≤ c → c ≤ 100 → 1 ≤ d → d ≤ 100 → a + b = c + d → F a ≠ F b → F c ≠ F d → F a + F b = F c + F d)
  (hs : ∀ x : Fin 3, ∃ n, 1 ≤ n ∧ n ≤ 100 ∧ F n = x) :
  (∃ σ : Equiv.Perm (Fin 3), ∀ n, 1 ≤ n → n ≤ 100 → F n = σ ((n-1 : ℕ) : Fin 3)) ∨
  (∃ σ : Equiv.Perm (Fin 3), ∀ n, 1 ≤ n → n ≤ 100 → F n = σ (if n = 1 then 0 else if n = 100 then 1 else 2)) := by
  have L1 : ∀ p q r x : Fin 3, p ≠ q → q ≠ r → p ≠ r → x ≠ p → x + p = q + r → False := by decide
  have L3 : ∀ p q r y : Fin 3, p ≠ q → r ≠ p → r ≠ q → y ≠ q → p + r = q + y → False := by decide
  have L4 : ∀ p q r z : Fin 3, p ≠ q → r ≠ p → r ≠ q → z ≠ p → p + z = q + r → False := by decide
  have L2 : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c → ∃ σ : Equiv.Perm (Fin 3), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by decide
  have L5 : ∀ p q : Fin 3, p ≠ q → -(p+q) ≠ p ∧ -(p+q) ≠ q := by decide
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℕ → Prop, ∀ i, Rb i ↔ (F i ≠ F (i+1) ∧ F (i+1) ≠ F (i+2) ∧ F i ≠ F (i+2)) := ⟨_, fun i => Iff.rfl⟩
  by_cases hr : ∃ k, 1 ≤ k ∧ k + 2 ≤ 100 ∧ Rb k
  · left
    obtain ⟨k, hk1, hk2, hk⟩ := hr
    have right : ∀ i, 1 ≤ i → i + 3 ≤ 100 → Rb i → F (i+3) = F i := by
      intro i h1 h2 h
      obtain ⟨a, b, c⟩ := (hRb i).1 h
      by_contra hne
      have := H (i+3) i (i+1) (i+2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hne b
      exact L1 _ _ _ _ a b c hne this
    have left : ∀ i, 2 ≤ i → i + 2 ≤ 100 → Rb i → F (i-1) = F (i+2) := by
      intro i h1 h2 h
      obtain ⟨a, b, c⟩ := (hRb i).1 h
      by_contra hne
      have := H (i-1) (i+2) i (i+1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hne a
      -- x + r = p + q
      revert this hne a b c
      generalize F (i-1) = x
      generalize F i = p
      generalize F (i+1) = q
      generalize F (i+2) = r
      revert x p q r
      decide
    have rs : ∀ i, 1 ≤ i → i + 3 ≤ 100 → Rb i → Rb (i+1) := by
      intro i h1 h2 h
      have e := right i h1 h2 h
      obtain ⟨a, b, c⟩ := (hRb i).1 h
      rw [hRb]
      have e3 : i + 1 + 1 = i + 2 := rfl
      have e4 : i + 1 + 2 = i + 3 := rfl
      rw [e3, e4, e]
      exact ⟨b, fun h => c h.symm, fun h => a h.symm⟩
    have ls : ∀ i, 2 ≤ i → i + 2 ≤ 100 → Rb i → Rb (i-1) := by
      intro i h1 h2 h
      have e := left i h1 h2 h
      obtain ⟨a, b, c⟩ := (hRb i).1 h
      rw [hRb]
      have e3 : i - 1 + 1 = i := by omega
      have e4 : i - 1 + 2 = i + 1 := by omega
      rw [e3, e4, e]
      exact ⟨fun h => c h.symm, a, fun h => b h.symm⟩
    have up : ∀ d, k + d + 2 ≤ 100 → Rb (k + d) := by
      intro d
      induction d with
      | zero => intro _; simpa using hk
      | succ d ih =>
        intro h
        have := rs (k+d) (by omega) (by omega) (ih (by omega))
        simpa [Nat.add_assoc] using this
    have down : ∀ d, d + 1 ≤ k → Rb (k - d) := by
      intro d
      induction d with
      | zero => intro _; simpa using hk
      | succ d ih =>
        intro h
        have := ls (k-d) (by omega) (by omega) (ih (by omega))
        have e : k - d - 1 = k - (d+1) := by omega
        rw [e] at this
        exact this
    have allRb : ∀ i, 1 ≤ i → i + 2 ≤ 100 → Rb i := by
      intro i h1 h2
      by_cases hik : k ≤ i
      · have := up (i - k) (by omega)
        have e : k + (i - k) = i := by omega
        rwa [e] at this
      · have := down (k - i) (by omega)
        have e : k - (k - i) = i := by omega
        rwa [e] at this
    have per : ∀ n, 1 ≤ n → n + 3 ≤ 100 → F (n+3) = F n := fun n h1 h2 => right n h1 h2 (allRb n h1 (by omega))
    obtain ⟨a, b, c⟩ := (hRb 1).1 (allRb 1 (by omega) (by omega))
    obtain ⟨σ, s0, s1, s2⟩ := L2 (F 1) (F 2) (F 3) a b c
    refine ⟨σ, ?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h1 h2
      by_cases hn : n ≤ 3
      · interval_cases n
        · simpa using s0.symm
        · simpa using s1.symm
        · simpa using s2.symm
      · have := per (n-3) (by omega) (by omega)
        have e : n - 3 + 3 = n := by omega
        rw [e] at this
        rw [this, ih (n-3) (by omega) (by omega) (by omega)]
        congr 1
        apply Fin.ext
        simp [Fin.val_natCast]
        omega
  · right
    push_neg at hr
    have T : ∀ i j, 1 ≤ i → i + 1 ≤ 100 → 1 ≤ j → j ≤ 100 → F i ≠ F (i+1) → F j ≠ F i → F j ≠ F (i+1) →
        (j = 1 ∨ j = 100) ∧ (j = 100 → F 99 = F (i+1)) ∧ (j = 1 → F 2 = F i) := by
      intro i j hi1 hi2 hj1 hj2 hne hji hjq
      have hL : 2 ≤ j → F (j-1) = F (i+1) := by
        intro hj
        by_contra hn
        have := H i j (i+1) (j-1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hji.symm (fun h => hn h.symm)
        exact L3 _ _ _ _ hne hji hjq (fun h => hn h) this
      have hR : j ≤ 99 → F (j+1) = F i := by
        intro hj
        by_contra hn
        have := H i (j+1) (i+1) j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hn hjq.symm
        exact L4 _ _ _ _ hne hji hjq hn this
      refine ⟨?_, ?_, ?_⟩
      · by_contra hn
        push_neg at hn
        have e1 : j - 1 + 1 = j := by omega
        have e2 : j - 1 + 2 = j + 1 := by omega
        apply hr (j-1) (by omega) (by omega)
        rw [hRb, e1, e2, hL (by omega), hR (by omega)]
        exact ⟨hjq.symm, hji, fun h => hne h.symm⟩
      · rintro rfl
        simpa using hL (by omega)
      · rintro rfl
        simpa using hR (by omega)
    have trans : ∃ i, 1 ≤ i ∧ i + 1 ≤ 100 ∧ F i ≠ F (i+1) := by
      by_contra hn
      push_neg at hn
      have all : ∀ n, 1 ≤ n → n ≤ 100 → F n = F 1 := by
        intro n
        induction n with
        | zero => intro h; omega
        | succ m ih =>
          intro h1 h2
          by_cases hm : m = 0
          · subst hm; rfl
          · rw [← hn m (by omega) (by omega)]; exact ih (by omega) (by omega)
      obtain ⟨n, h1, h2, h3⟩ := hs (F 1 + 1)
      rw [all n h1 h2] at h3
      revert h3
      generalize F 1 = x
      revert x
      decide
    obtain ⟨i, hi1, hi2, hne⟩ := trans
    obtain ⟨j, hj1, hj2, hj⟩ := hs (-(F i + F (i+1)))
    obtain ⟨n1, n2⟩ := L5 _ _ hne
    rw [hj] at *
    obtain ⟨T1, T2, T3⟩ := T i j hi1 hi2 hj1 hj2 hne (by rw [hj]; exact n1) (by rw [hj]; exact n2)
    sorry
