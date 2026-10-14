import Mathlib

open Function

/--
Let $S$ be a set of ordered triples $(a, b, c)$ of distinct elements of a finite set $A$. Suppose that \begin{enumerate} \item $(a,b,c) \in S$ if and only if $(b,c,a) \in S$; \item $(a,b,c) \in S$ if and only if $(c,b,a) \notin S$; \item $(a,b,c)$ and $(c,d,a)$ are both in $S$ if and only if $(b,c,d)$ and $(d,a,b)$ are both in $S$. \end{enumerate} Prove that there exists a one-to-one function $g$ from $A$ to $\R$ such that $g(a) < g(b) < g(c)$ implies $(a,b,c) \in S$.
-/
theorem putnam_1996_a4
(A : Type*)
[Finite A]
(S : Set (A × A × A))
(hSdistinct : ∀ a b c : A, ⟨a, b, c⟩ ∈ S → a ≠ b ∧ b ≠ c ∧ a ≠ c)
(hS1 : ∀ a b c : A, [a,b,c].Pairwise (· ≠ ·) → (⟨a, b, c⟩ ∈ S ↔ ⟨b, c, a⟩ ∈ S))
(hS2 : ∀ a b c : A, [a,b,c].Pairwise (· ≠ ·) → (⟨a, b, c⟩ ∈ S ↔ ⟨c, b, a⟩ ∉ S))
(hS3 : ∀ a b c d : A, [a,b,c,d].Pairwise (· ≠ ·) → ((⟨a, b, c⟩ ∈ S ∧ ⟨c, d, a⟩ ∈ S) ↔ (⟨b,c,d⟩ ∈ S ∧ ⟨d,a,b⟩ ∈ S)))
: ∃ g : A → ℝ, Injective g ∧ (∀ a b c : A, g a < g b ∧ g b < g c → ⟨a,b,c⟩ ∈ S) :=
by
  classical
  have := Fintype.ofFinite A
  rcases isEmpty_or_nonempty A with hA | ⟨⟨x⟩⟩
  · exact ⟨fun _ => 0, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  have asym : ∀ a b : A, ⟨x, a, b⟩ ∈ S → ⟨x, b, a⟩ ∉ S := by
    intro a b h h'
    obtain ⟨h1, h2, h3⟩ := hSdistinct _ _ _ h
    have e2 := hS2 x a b (by simp <;> grind)
    have e3 := hS1 b a x (by simp <;> grind)
    have e4 := hS1 a x b (by simp <;> grind)
    exact (e2.1 h) (e3.2 (e4.2 h'))
  have tot : ∀ a b : A, a ≠ x → b ≠ x → a ≠ b → ⟨x, a, b⟩ ∈ S ∨ ⟨x, b, a⟩ ∈ S := by
    intro a b h1 h2 h3
    by_contra hc
    push_neg at hc
    have e2 := hS2 x a b (by simp <;> grind)
    have e3 := hS1 b a x (by simp <;> grind)
    have e4 := hS1 a x b (by simp <;> grind)
    exact hc.1 (e2.2 (fun h => hc.2 (e4.1 (e3.1 h))))
  have K : ∀ a b c : A, ⟨x, a, b⟩ ∈ S → ⟨x, b, c⟩ ∈ S → ⟨x, a, c⟩ ∈ S ∧ ⟨a, b, c⟩ ∈ S := by
    intro a b c h h'
    obtain ⟨h1, h2, h3⟩ := hSdistinct _ _ _ h
    obtain ⟨h4, h5, h6⟩ := hSdistinct _ _ _ h'
    have hac : a ≠ c := by
      rintro rfl
      exact asym _ _ h h'
    have e := hS3 x a b c (by simp <;> grind)
    have e1 := hS1 x b c (by simp <;> grind)
    obtain ⟨p, q⟩ := e.1 ⟨h, e1.1 h'⟩
    have e2 := hS1 c x a (by simp <;> grind)
    exact ⟨e2.1 q, p⟩
  let lt : A → A → Prop := fun a b => (a = x ∧ b ≠ x) ∨ (a ≠ x ∧ b ≠ x ∧ ⟨x, a, b⟩ ∈ S)
  have irr : ∀ a, ¬ lt a a := by
    intro a h
    rcases h with h | h
    · exact h.2 h.1
    · exact (hSdistinct _ _ _ h.2.2).2.1 rfl
  have trans : ∀ a b c, lt a b → lt b c → lt a c := by
    intro a b c h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact (h.2 h'.1).elim
    · exact Or.inl ⟨h.1, h'.2.1⟩
    · exact (h.2.1 h'.1).elim
    · exact Or.inr ⟨h.1, h'.2.1, (K _ _ _ h.2.2 h'.2.2).1⟩
  have trich : ∀ a b, a ≠ b → lt a b ∨ lt b a := by
    intro a b hab
    by_cases ha : a = x
    · exact Or.inl (Or.inl ⟨ha, fun hb => hab (ha.trans hb.symm)⟩)
    by_cases hb : b = x
    · exact Or.inr (Or.inl ⟨hb, ha⟩)
    rcases tot a b ha hb hab with h | h
    · exact Or.inl (Or.inr ⟨ha, hb, h⟩)
    · exact Or.inr (Or.inr ⟨hb, ha, h⟩)
  let g : A → ℝ := fun a => ((Finset.univ.filter (fun b => lt b a)).card : ℝ)
  have mono : ∀ a b, lt a b → g a < g b := by
    intro a b h
    simp only [g]
    exact_mod_cast Finset.card_lt_card (by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨a, by simp [h], by simp [irr]⟩
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact trans _ _ _ hc h)
  have back : ∀ a b, g a < g b → lt a b := by
    intro a b h
    by_cases hab : a = b
    · subst hab; exact absurd h (lt_irrefl _)
    rcases trich a b hab with h' | h'
    · exact h'
    · exact absurd (mono _ _ h') (not_lt.2 h.le)
  refine ⟨g, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    rcases trich a b hne with h | h
    · exact absurd (mono _ _ h) (by rw [hab]; exact lt_irrefl _)
    · exact absurd (mono _ _ h) (by rw [hab]; exact lt_irrefl _)
  · intro a b c ⟨h1, h2⟩
    have l1 := back _ _ h1
    have l2 := back _ _ h2
    rcases l1 with l1 | l1
    · rw [l1.1]
      rcases l2 with l2 | l2
      · exact (l1.2 l2.1).elim
      · exact l2.2.2
    · rcases l2 with l2 | l2
      · exact absurd l2.1 l1.2.1
      · exact (K _ _ _ l1.2.2 l2.2.2).2
