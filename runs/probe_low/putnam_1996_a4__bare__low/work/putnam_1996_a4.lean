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
  haveI := Fintype.ofFinite A
  by_cases hA : Nonempty A
  swap
  · exact ⟨fun _ => 0, fun a => absurd ⟨a⟩ hA, fun a => absurd ⟨a⟩ hA⟩
  obtain ⟨z⟩ := hA
  have trans : ∀ x y w, (⟨z,x,y⟩ : A × A × A) ∈ S → (⟨z,y,w⟩ : A × A × A) ∈ S → (⟨z,x,w⟩ : A × A × A) ∈ S := by
    intro x y w h1 h2
    obtain ⟨a1,a2,a3⟩ := hSdistinct _ _ _ h1
    obtain ⟨b1,b2,b3⟩ := hSdistinct _ _ _ h2
    have hxw : x ≠ w := by
      rintro rfl
      have := (hS2 z x y (by simp [a1,a2,a3,b1,b2,b3,a1.symm,a2.symm,a3.symm,b1.symm,b2.symm,b3.symm])).1 h1
      exact this ((hS1 z y x (by simp [a1,a2,a3,b1,b2,b3,a1.symm,a2.symm,a3.symm,b1.symm,b2.symm,b3.symm])).1 h2)
    have h2' : (⟨y,w,z⟩ : A × A × A) ∈ S := (hS1 z y w (by simp [a1,a2,a3,b1,b2,b3,hxw,hxw.symm,a1.symm,a2.symm,a3.symm,b1.symm,b2.symm,b3.symm])).1 h2
    have := ((hS3 z x y w (by simp [a1,a2,a3,b1,b2,b3,hxw,hxw.symm,a1.symm,a2.symm,a3.symm,b1.symm,b2.symm,b3.symm])).1 ⟨h1, h2'⟩).2
    exact (hS1 w z x (by simp [a1,a2,a3,b1,b2,b3,hxw,hxw.symm,a1.symm,a2.symm,a3.symm,b1.symm,b2.symm,b3.symm])).1 this
  have total : ∀ x y, x ≠ z → y ≠ z → x ≠ y → (⟨z,x,y⟩ : A × A × A) ∈ S ∨ (⟨z,y,x⟩ : A × A × A) ∈ S := by
    intro x y hx hy hxy
    by_cases h : (⟨z,x,y⟩ : A × A × A) ∈ S
    · exact Or.inl h
    · right
      have h' : (⟨y,x,z⟩ : A × A × A) ∈ S := by
        by_contra h''
        exact h ((hS2 z x y (by simp [hx, hy, hxy, hx.symm, hy.symm, hxy.symm])).2 h'')
      exact (hS1 z y x (by simp [hx, hy, hxy, hx.symm, hy.symm, hxy.symm])).2 h'
  let g : A → ℝ := fun x => if x = z then 0 else ((Finset.univ.filter (fun w => (⟨z,w,x⟩ : A × A × A) ∈ S)).card : ℝ) + 1
  have gz : g z = 0 := by simp [g]
  have gpos : ∀ x, x ≠ z → 0 < g x := by
    intro x hx; simp only [g, hx, if_false]; positivity
  have mono : ∀ x y, (⟨z,x,y⟩ : A × A × A) ∈ S → g x < g y := by
    intro x y h
    obtain ⟨a1,a2,a3⟩ := hSdistinct _ _ _ h
    simp only [g, a1.symm, a3.symm, if_false]
    have : (Finset.univ.filter (fun w => (⟨z,w,x⟩ : A × A × A) ∈ S)).card < (Finset.univ.filter (fun w => (⟨z,w,y⟩ : A × A × A) ∈ S)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨x, by simp [h], by simp; intro hh; exact (hSdistinct _ _ _ hh).2.1 rfl⟩
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact trans _ _ _ hw h
    have : ((Finset.univ.filter (fun w => (⟨z,w,x⟩ : A × A × A) ∈ S)).card : ℝ) < ((Finset.univ.filter (fun w => (⟨z,w,y⟩ : A × A × A) ∈ S)).card : ℝ) := by exact_mod_cast this
    linarith
  have key : ∀ x y, x ≠ z → y ≠ z → g x < g y → (⟨z,x,y⟩ : A × A × A) ∈ S := by
    intro x y hx hy hlt
    by_contra h
    have hxy : x ≠ y := by rintro rfl; exact lt_irrefl _ hlt
    rcases total x y hx hy hxy with h1 | h1
    · exact h h1
    · have := mono _ _ h1; linarith
  refine ⟨g, ?_, ?_⟩
  · intro x y hxy
    by_contra hne
    by_cases hx : x = z
    · subst hx; have := gpos y (Ne.symm hne); linarith
    by_cases hy : y = z
    · subst hy; have := gpos x hx; linarith
    rcases total x y hx hy hne with h | h
    · have := mono _ _ h; linarith
    · have := mono _ _ h; linarith
  · intro a b c ⟨h1, h2⟩
    have hb : b ≠ z := by rintro rfl; have : 0 ≤ g a := by
                            by_cases ha : a = b
                            · subst ha; simp [gz]
                            · exact (gpos a ha).le
                          linarith
    have hc : c ≠ z := by rintro rfl; have := gpos b hb; linarith
    have hbc := key b c hb hc h2
    by_cases ha : a = z
    · subst ha; exact hbc
    have hab := key a b ha hb h1
    have hac := key a c ha hc (h1.trans h2)
    obtain ⟨d1,d2,d3⟩ := hSdistinct _ _ _ hab
    obtain ⟨e1,e2,e3⟩ := hSdistinct _ _ _ hbc
    obtain ⟨f1,f2,f3⟩ := hSdistinct _ _ _ hac
    have := ((hS3 z a b c (by simp [ha, hb, hc, (show a ≠ z from ha).symm, (show b ≠ z from hb).symm, (show c ≠ z from hc).symm, d1, d2, e2, f2, f2.symm, d3, d1.symm, d2.symm, e2.symm, d3.symm])).1 ⟨hab, (hS1 z b c (by simp [d1, d2, d3, e1, e2, e3, d1.symm, d2.symm, d3.symm, e1.symm, e2.symm, e3.symm])).1 hbc⟩).1
    exact this
