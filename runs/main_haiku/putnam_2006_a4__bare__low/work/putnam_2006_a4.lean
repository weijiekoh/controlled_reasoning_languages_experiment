import Mathlib

-- Note: uses (ℕ → ℕ) instead of (Equiv.Perm (Fin n))
noncomputable abbrev putnam_2006_a4_solution : ℕ → ℝ := (fun n : ℕ => (n + 1) / 3)
/--
Let $S=\{1,2,\dots,n\}$ for some integer $n>1$. Say a permutation $\pi$ of $S$ has a \emph{local maximum} at $k \in S$ if
\begin{enumerate}
\item[(i)] $\pi(k)>\pi(k+1)$ for $k=1$;
\item[(ii)] $\pi(k-1)<\pi(k)$ and $\pi(k)>\pi(k+1)$ for $1< k< n$;
\item[(iii)] $\pi(k-1)<\pi(k)$ for $k=n$.
\end{enumerate}
(For example, if $n=5$ and $\pi$ takes values at $1,2,3,4,5$ of $2,1,4,5,3$, then $\pi$ has a local maximum of 2 at $k=1$, and a local maximum of 5 at $k=4$.) What is the average number of local maxima of a permutation of $S$, averaging over all permutations of $S$?
-/
theorem putnam_2006_a4
(n : ℕ)
(pnat : Equiv.Perm (Fin n) → (ℕ → ℕ))
(pcount : Equiv.Perm (Fin n) → ℕ)
(ngt1 : n > 1)
(hpnat : ∀ p : Equiv.Perm (Fin n), ∀ k : Fin n, (pnat p) k = p k)
(hpcount : ∀ p : Equiv.Perm (Fin n), pcount p = {k : Fin n | (k.1 = 0 ∨ (pnat p) (k - 1) < (pnat p) k) ∧ (k = n - 1 ∨ (pnat p) k > (pnat p) (k + 1))}.encard)
: (∑ p : Equiv.Perm (Fin n), pcount p) / {p : Equiv.Perm (Fin n) | true}.ncard = putnam_2006_a4_solution n := by
  classical
  have hq' : ∀ (p : Equiv.Perm (Fin n)) (i : ℕ) (h : i < n), pnat p i = (p ⟨i, h⟩ : ℕ) := by
    intro p i h
    have := hpnat p ⟨i, h⟩
    simpa using this
  have hcount : ∀ p : Equiv.Perm (Fin n), pcount p = ∑ k : Fin n, (if ((k.1 = 0 ∨ (pnat p) (k.1 - 1) < (pnat p) k.1) ∧ (k.1 = n - 1 ∨ (pnat p) k.1 > (pnat p) (k.1 + 1))) then 1 else 0) := by
    intro p
    have h := hpcount p
    simp only [Set.encard_eq_coe_toFinset_card, Set.toFinset_setOf] at h
    rw [Finset.card_filter] at h
    exact_mod_cast h
  have two : ∀ x y : Fin n, x ≠ y →
      2 * ∑ p : Equiv.Perm (Fin n), (if (p x : ℕ) < p y then 1 else 0) = Fintype.card (Equiv.Perm (Fin n)) := by
    intro x y hxy
    have hsw := Equiv.sum_comp (Equiv.mulRight (Equiv.swap x y))
      (fun p : Equiv.Perm (Fin n) => if (p x : ℕ) < p y then 1 else 0)
    simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right] at hsw
    have hpt : ∀ p : Equiv.Perm (Fin n),
        (if (p x : ℕ) < p y then 1 else 0) + (if (p y : ℕ) < p x then 1 else 0) = 1 := by
      intro p
      have h1 : (p x : ℕ) ≠ p y := fun h => hxy (p.injective (Fin.ext h))
      split_ifs <;> omega
    have hs := Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => hpt p)
    rw [Finset.sum_add_distrib, hsw] at hs
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hs
    omega
  have L : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c →
      ∑ p : Equiv.Perm (Fin n), (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        = ∑ p : Equiv.Perm (Fin n), (if (p a : ℕ) < p b ∧ (p c : ℕ) < p b then 1 else 0) := by
    intro a b c hab hac hbc
    have hsw := Equiv.sum_comp (Equiv.mulRight (Equiv.swap a b))
      (fun p : Equiv.Perm (Fin n) => if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
    simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm] at hsw
    exact hsw.symm
  have conj : ∀ a b c : Fin n,
      ∑ p : Equiv.Perm (Fin n), (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        = ∑ p : Equiv.Perm (Fin n), (if (p c : ℕ) < p a ∧ (p b : ℕ) < p a then 1 else 0) := by
    intro a b c
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h1 : (p b : ℕ) < p a <;> by_cases h2 : (p c : ℕ) < p a <;> simp [h1, h2]
  have trip : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c →
      3 * ∑ p : Equiv.Perm (Fin n), (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        = Fintype.card (Equiv.Perm (Fin n)) := by
    intro a b c hab hac hbc
    have hpt : ∀ p : Equiv.Perm (Fin n),
        (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        + (if (p a : ℕ) < p b ∧ (p c : ℕ) < p b then 1 else 0)
        + (if (p a : ℕ) < p c ∧ (p b : ℕ) < p c then 1 else 0) = 1 := by
      intro p
      have h1 : (p a : ℕ) ≠ p b := fun h => hab (p.injective (Fin.ext h))
      have h2 : (p a : ℕ) ≠ p c := fun h => hac (p.injective (Fin.ext h))
      have h3 : (p b : ℕ) ≠ p c := fun h => hbc (p.injective (Fin.ext h))
      split_ifs <;> omega
    have hs := Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => hpt p)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hs
    have e1 := L a b c hab hac hbc
    have e2 : ∑ p : Equiv.Perm (Fin n), (if (p a : ℕ) < p c ∧ (p b : ℕ) < p c then 1 else 0)
        = ∑ p : Equiv.Perm (Fin n), (if (p a : ℕ) < p b ∧ (p c : ℕ) < p b then 1 else 0) := by
      rw [conj c a b, L c b a hbc.symm hac.symm hab.symm, conj b c a]
    omega
  have perk : ∀ k : Fin n, 6 * ∑ p : Equiv.Perm (Fin n),
      (if ((k.1 = 0 ∨ (pnat p) (k.1 - 1) < (pnat p) k.1) ∧ (k.1 = n - 1 ∨ (pnat p) k.1 > (pnat p) (k.1 + 1))) then 1 else 0)
      = 2 * Fintype.card (Equiv.Perm (Fin n)) + (if (k.1 = 0 ∨ k.1 = n - 1) then Fintype.card (Equiv.Perm (Fin n)) else 0) := by
    intro k
    obtain ⟨j, hj⟩ := k
    dsimp only
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      have h1 : 1 < n := ngt1
      have key : ∀ p : Equiv.Perm (Fin n),
          (if ((0 = 0 ∨ (pnat p) (0 - 1) < (pnat p) 0) ∧ (0 = n - 1 ∨ (pnat p) 0 > (pnat p) (0 + 1))) then 1 else 0)
          = (if (p ⟨1, h1⟩ : ℕ) < p ⟨0, hj⟩ then 1 else 0) := by
        intro p
        have hne : ¬ ((0:ℕ) = n - 1) := by omega
        refine if_congr ?_ rfl rfl
        rw [hq' p 0 hj, hq' p 1 h1]
        constructor
        · intro h; exact h.2.resolve_left hne
        · intro h; exact ⟨Or.inl rfl, Or.inr h⟩
      rw [Finset.sum_congr rfl (fun p _ => key p)]
      have ht := two ⟨1, h1⟩ ⟨0, hj⟩ (fun h => by simp [Fin.ext_iff] at h)
      rw [if_pos (show (0:ℕ) = 0 ∨ (0:ℕ) = n - 1 from Or.inl rfl)]
      omega
    · by_cases hn : j = n - 1
      · have hne0 : j ≠ 0 := by omega
        have key : ∀ p : Equiv.Perm (Fin n),
            (if ((j = 0 ∨ (pnat p) (j - 1) < (pnat p) j) ∧ (j = n - 1 ∨ (pnat p) j > (pnat p) (j + 1))) then 1 else 0)
            = (if (p ⟨j - 1, by omega⟩ : ℕ) < p ⟨j, hj⟩ then 1 else 0) := by
          intro p
          refine if_congr ?_ rfl rfl
          rw [hq' p j hj, hq' p (j - 1) (by omega)]
          constructor
          · intro h; exact h.1.resolve_left hne0
          · intro h; exact ⟨Or.inr h, Or.inl hn⟩
        rw [Finset.sum_congr rfl (fun p _ => key p)]
        have ht := two ⟨j - 1, by omega⟩ ⟨j, hj⟩ (fun h => by simp [Fin.ext_iff] at h; omega)
        rw [if_pos (show j = 0 ∨ j = n - 1 from Or.inr hn)]
        omega
      · have hne0 : j ≠ 0 := by omega
        have key : ∀ p : Equiv.Perm (Fin n),
            (if ((j = 0 ∨ (pnat p) (j - 1) < (pnat p) j) ∧ (j = n - 1 ∨ (pnat p) j > (pnat p) (j + 1))) then 1 else 0)
            = (if (p ⟨j - 1, by omega⟩ : ℕ) < p ⟨j, hj⟩ ∧ (p ⟨j + 1, by omega⟩ : ℕ) < p ⟨j, hj⟩ then 1 else 0) := by
          intro p
          refine if_congr ?_ rfl rfl
          rw [hq' p j hj, hq' p (j - 1) (by omega), hq' p (j + 1) (by omega)]
          constructor
          · intro h; exact ⟨h.1.resolve_left hne0, h.2.resolve_left hn⟩
          · intro h; exact ⟨Or.inr h.1, Or.inr h.2⟩
        rw [Finset.sum_congr rfl (fun p _ => key p)]
        have ht := trip ⟨j, hj⟩ ⟨j - 1, by omega⟩ ⟨j + 1, by omega⟩
          (fun h => by simp [Fin.ext_iff] at h; omega) (fun h => by simp [Fin.ext_iff] at h)
          (fun h => by simp [Fin.ext_iff] at h)
        rw [if_neg (show ¬ (j = 0 ∨ j = n - 1) from fun h => h.elim hne0 hn)]
        omega
  have htot : 6 * ∑ p, pcount p = ∑ k : Fin n, (2 * Fintype.card (Equiv.Perm (Fin n))
      + (if (k.1 = 0 ∨ k.1 = n - 1) then Fintype.card (Equiv.Perm (Fin n)) else 0)) := by
    rw [Finset.sum_congr rfl (fun p _ => hcount p), Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => perk k)
  have hite : ∑ k : Fin n, (if (k.1 = 0 ∨ k.1 = n - 1) then Fintype.card (Equiv.Perm (Fin n)) else 0)
      = 2 * Fintype.card (Equiv.Perm (Fin n)) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    generalize Fintype.card (Equiv.Perm (Fin (m + 2))) = C
    have h1 : ∑ x : Fin (m + 1), (if (x : ℕ) = m then C else 0) = C := by
      rw [Fin.sum_univ_eq_sum_range (fun i => if i = m then C else 0) (m + 1)]
      simp
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have h2 : ∑ x : Fin m, (if ((x : ℕ) + 1 = 0 ∨ (x : ℕ) + 1 = m + 2 - 1) then C else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      have := i.isLt
      omega
    simp only [Fin.val_zero, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]
    rw [h2]
    simp
    ring
  
  rw [Finset.sum_add_distrib, hite] at htot
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at htot
  have h3 : 3 * ∑ p, pcount p = (n + 1) * Fintype.card (Equiv.Perm (Fin n)) := by
    nlinarith
  have hset : ({p : Equiv.Perm (Fin n) | true}).ncard = Fintype.card (Equiv.Perm (Fin n)) := by
    simp only [eq_self_iff_true, Set.setOf_true]
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  rw [hset]
  have hpos : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  have h3r : (3:ℝ) * ((∑ p, pcount p : ℕ) : ℝ) = ((n:ℝ) + 1) * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast h3
  simp only [putnam_2006_a4_solution]
  rw [div_eq_iff hpos]
  push_cast at h3r ⊢
  linarith
