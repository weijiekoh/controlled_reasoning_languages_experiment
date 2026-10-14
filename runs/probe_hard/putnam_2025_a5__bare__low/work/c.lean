
def altL (a : ℤˣ) : ℕ → List ℤˣ
  | 0 => []
  | k+1 => a :: altL (-a) k

lemma altL_len (a : ℤˣ) (k : ℕ) : (altL a k).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [altL, ih]

lemma altL_neg (a : ℤˣ) (k : ℕ) : altL (-a) k = ng (altL a k) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [altL, ng, List.map_cons, List.map_map] at ih ⊢; have := ih (-a); rw [neg_neg] at this; rw [this]

lemma altL_snoc (a : ℤˣ) (k : ℕ) : ∃ c, altL a (k+1) = altL a k ++ [c] ∧ altL a (k+2) = altL a k ++ [c, -c] := by
  induction k generalizing a with
  | zero => exact ⟨a, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨c, h1, h2⟩ := ih (-a)
    refine ⟨c, ?_, ?_⟩
    · show a :: altL (-a) (k+1) = a :: altL (-a) k ++ [c]
      rw [h1]; rfl
    · show a :: altL (-a) (k+2) = a :: altL (-a) k ++ [c, -c]
      rw [h2]; rfl

lemma neg_of_ne (b c : ℤˣ) (h : b ≠ c) : b = -c := by
  rcases Int.units_eq_one_or b with rfl | rfl <;> rcases Int.units_eq_one_or c with rfl | rfl <;> first | rfl | exact absurd rfl h | decide

lemma Zlem : ∀ (d k : ℕ) (a : ℤˣ) (rest : List ℤˣ), 1 ≤ k → rest.length = d →
    FF (altL a k ++ rest) ≤ FF (altL a (k + d)) := by
  intro d
  induction d with
  | zero =>
    intro k a rest _ hr
    have : rest = [] := List.length_eq_zero_iff.mp hr
    subst this
    simp
  | succ d ih =>
    intro k a rest hk hr
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, rest', rfl⟩ : ∃ b rest', rest = b :: rest' := by
      cases rest with
      | nil => simp at hr
      | cons b r => exact ⟨b, r, rfl⟩
    have hr' : rest'.length = d := by simpa using hr
    obtain ⟨c, h1, h2⟩ := altL_snoc a j
    by_cases hb : b = c
    · subst hb
      have e1 : altL a (j+1) ++ b :: rest' = altL a j ++ b :: b :: rest' := by rw [h1]; simp
      have e2 : altL a j ++ b :: ng (b :: rest') = altL a (j+2) ++ ng rest' := by
        rw [h2]; simp [ng]
      have := flip_gt (altL a j) b rest'
      rw [e1]
      refine le_trans this.le ?_
      rw [e2]
      have := ih (j+2) a (ng rest') (by omega) (by rw [ng_length]; exact hr')
      rw [show j + 1 + (d + 1) = j + 2 + d by omega]
      exact this
    · have hb' := neg_of_ne b c hb
      have e1 : altL a (j+1) ++ b :: rest' = altL a (j+2) ++ rest' := by
        rw [h1, h2, hb']; simp
      rw [e1]
      have := ih (j+2) a rest' (by omega) hr'
      rw [show j + 1 + (d + 1) = j + 2 + d by omega]
      exact this

lemma decomp : ∀ (l : List ℤˣ) (a : ℤˣ), (∃ pre c rest, l = pre ++ c :: c :: rest) ∨
    l = altL a l.length ∨ (∃ b l₁, l = b :: l₁ ∧ b ≠ a) := by
  intro l
  induction l with
  | nil => intro a; exact Or.inr (Or.inl rfl)
  | cons b l₁ ih =>
    intro a
    by_cases hba : b = a
    · subst hba
      rcases ih (-b) with ⟨pre, c, rest, h⟩ | h | ⟨b', l₂, h, hne⟩
      · exact Or.inl ⟨b :: pre, c, rest, by simp [h]⟩
      · exact Or.inr (Or.inl (by simp [altL, ← h]))
      · have : b' = b := by have := neg_of_ne b' (-b) hne; simpa using this
        subst this
        exact Or.inl ⟨[], b', l₂, by simp [h]⟩
    · exact Or.inr (Or.inr ⟨b, l₁, rfl, hba⟩)

lemma ofFn_alt (a : ℤˣ) : ∀ (n : ℕ) (s : Fin n → ℤˣ), (∀ i : Fin n, s i = a * (-1)^i.val) → List.ofFn s = altL a n := by
  intro n
  induction n generalizing a with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    rw [List.ofFn_succ]
    simp only [altL]
    congr 1
    · simpa using h 0
    · apply ih
      intro i
      rw [h i.succ]
      simp [pow_succ]
      
lemma alt_ofFn (a : ℤˣ) : ∀ (n : ℕ) (s : Fin n → ℤˣ), List.ofFn s = altL a n → (∀ i : Fin n, s i = a * (-1)^i.val) := by
  intro n
  induction n generalizing a with
  | zero => intro s _ i; exact i.elim0
  | succ n ih =>
    intro s h i
    rw [List.ofFn_succ] at h
    simp only [altL, List.cons.injEq] at h
    induction i using Fin.cases with
    | zero => simpa using h.1
    | succ i =>
      have := ih (-a) _ h.2 i
      rw [this]
      simp [pow_succ]

lemma f_eq (n : ℕ) (s : Fin n → ℤˣ) : f n s = FF (List.ofFn s) := by
  unfold f FF
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin (n+1)) => σ 0) (t := univ) (by simp)]
  have : ∀ y : Fin (n+1), (({σ : Equiv.Perm (Fin (n + 1)) |
      ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))}).filter (fun σ => σ 0 = y)).card
      = W (List.ofFn s) y.val := by
    intro y
    rw [← partA n s y]
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    tauto
  rw [sum_congr rfl (fun y _ => this y)]
  rw [Fin.sum_univ_eq_sum_range (fun y => W (List.ofFn s) y) (n+1)]
  simp

lemma exists_ofFn (n : ℕ) (l' : List ℤˣ) (h : l'.length = n) : ∃ t : Fin n → ℤˣ, List.ofFn t = l' := by
  subst h; exact ⟨l'.get, List.ofFn_get l'⟩

lemma FF_alt (a b : ℤˣ) (n : ℕ) : FF (altL a n) = FF (altL b n) := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl
  · rfl
  · rw [altL_neg 1 n, FF_ng]
  · rw [altL_neg 1 n, FF_ng]
  · rfl
