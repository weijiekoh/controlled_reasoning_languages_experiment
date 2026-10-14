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
: (∑ p : Equiv.Perm (Fin n), pcount p) / {p : Equiv.Perm (Fin n) | true}.ncard = putnam_2006_a4_solution n :=
by
  have hP : ∀ (p : Equiv.Perm (Fin n)) (m : ℕ) (h : m < n), pnat p m = ((p ⟨m, h⟩ : Fin n) : ℕ) := by
    intro p m h
    exact hpnat p ⟨m, h⟩
  have hinj : ∀ (p : Equiv.Perm (Fin n)) (a b : Fin n), a ≠ b → (p a : ℕ) ≠ (p b : ℕ) := by
    intro p a b hab h
    exact hab (p.injective (Fin.ext h))
  have H1 : ∀ x y z : Fin n, x ≠ y → z ≠ x → z ≠ y →
      (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x ∧ (p z : ℕ) < p x)).card =
      (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p x : ℕ) < p y ∧ (p z : ℕ) < p y)).card := by
    intro x y z hxy hzx hzy
    apply Finset.card_nbij' (fun p => p * Equiv.swap x y) (fun p => p * Equiv.swap x y)
    · intro p hp
      simp only [Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_ofPred_eq, Equiv.Perm.mul_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hzx hzy] at hp ⊢
      exact hp
    · intro p hp
      simp only [Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_ofPred_eq, Equiv.Perm.mul_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hzx hzy] at hp ⊢
      exact hp
    · intro p _
      ext w
      simp [Equiv.Perm.mul_apply]
    · intro p _
      ext w
      simp [Equiv.Perm.mul_apply]
  have hpair : ∀ x y : Fin n, x ≠ y →
      2 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x)).card = n.factorial := by
    intro x y hxy
    have hc : (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x)).card =
        (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p x : ℕ) < p y)).card := by
      apply Finset.card_nbij' (fun p => p * Equiv.swap x y) (fun p => p * Equiv.swap x y)
      · intro p hp
        simp only [Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_ofPred_eq, Equiv.Perm.mul_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right] at hp ⊢
        exact hp
      · intro p hp
        simp only [Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_ofPred_eq, Equiv.Perm.mul_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right] at hp ⊢
        exact hp
      · intro p _
        ext w
        simp [Equiv.Perm.mul_apply]
      · intro p _
        ext w
        simp [Equiv.Perm.mul_apply]
    have hsplit : (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x)).card +
        (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => ¬ ((p y : ℕ) < p x))).card = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : (p y : ℕ) < p x <;> simp [h]
    have hneg : (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => ¬ ((p y : ℕ) < p x))) =
        Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p x : ℕ) < p y) := by
      apply Finset.filter_congr
      intro p _
      have := hinj p x y hxy
      omega
    rw [hneg, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsplit
    rw [hc]
    omega
  have htri : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z →
      3 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x ∧ (p z : ℕ) < p x)).card = n.factorial := by
    intro x y z hxy hxz hyz
    have e1 := H1 x y z hxy (Ne.symm hxz) (Ne.symm hyz)
    have e2 := H1 x z y hxz (Ne.symm hxy) hyz
    have e2' : (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x ∧ (p z : ℕ) < p x)).card =
        (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p x : ℕ) < p z ∧ (p y : ℕ) < p z)).card := by
      have hq : Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x ∧ (p z : ℕ) < p x) =
          Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p z : ℕ) < p x ∧ (p y : ℕ) < p x) := by
        exact Finset.filter_congr (fun p _ => and_comm)
      rw [hq, e2]
    have hpt : ∀ p : Equiv.Perm (Fin n),
        (if (p y : ℕ) < p x ∧ (p z : ℕ) < p x then 1 else 0) +
        (if (p x : ℕ) < p y ∧ (p z : ℕ) < p y then 1 else 0) +
        (if (p x : ℕ) < p z ∧ (p y : ℕ) < p z then 1 else 0) = 1 := by
      intro p
      have h1 := hinj p x y hxy
      have h2 := hinj p x z hxz
      have h3 := hinj p y z hyz
      split_ifs <;> omega
    have hsum3 : (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p y : ℕ) < p x ∧ (p z : ℕ) < p x)).card +
        (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p x : ℕ) < p y ∧ (p z : ℕ) < p y)).card +
        (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p x : ℕ) < p z ∧ (p y : ℕ) < p z)).card = n.factorial := by
      simp only [Finset.card_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun p _ => hpt p)]
      simp [Fintype.card_perm]
    omega
  have hcount : ∀ p : Equiv.Perm (Fin n), pcount p =
      (Finset.univ.filter (fun k : Fin n => ((k:ℕ) = 0 ∨ pnat p ((k:ℕ) - 1) < pnat p k) ∧
        ((k:ℕ) = n - 1 ∨ pnat p k > pnat p ((k:ℕ) + 1)))).card := by
    intro p
    have h := hpcount p
    have e : {k : Fin n | ((k:ℕ) = 0 ∨ pnat p ((k:ℕ) - 1) < pnat p k) ∧
        ((k:ℕ) = n - 1 ∨ pnat p k > pnat p ((k:ℕ) + 1))} =
        ↑(Finset.univ.filter (fun k : Fin n => ((k:ℕ) = 0 ∨ pnat p ((k:ℕ) - 1) < pnat p k) ∧
          ((k:ℕ) = n - 1 ∨ pnat p k > pnat p ((k:ℕ) + 1)))) := by
      ext k
      simp
    rw [e, Set.encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  have hsum : ∑ p : Equiv.Perm (Fin n), pcount p =
      ∑ k : Fin n, (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => ((k:ℕ) = 0 ∨ pnat p ((k:ℕ) - 1) < pnat p k) ∧
        ((k:ℕ) = n - 1 ∨ pnat p k > pnat p ((k:ℕ) + 1)))).card := by
    simp only [hcount, Finset.card_filter]
    exact Finset.sum_comm
  have hper : ∀ k : Fin n, 6 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => ((k:ℕ) = 0 ∨ pnat p ((k:ℕ) - 1) < pnat p k) ∧
        ((k:ℕ) = n - 1 ∨ pnat p k > pnat p ((k:ℕ) + 1)))).card =
      n.factorial * (if ((k:ℕ) = 0 ∨ (k:ℕ) = n - 1) then 3 else 2) := by
    rintro ⟨k, hk⟩
    show 6 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (k = 0 ∨ pnat p (k - 1) < pnat p k) ∧
        (k = n - 1 ∨ pnat p k > pnat p (k + 1)))).card = n.factorial * (if (k = 0 ∨ k = n - 1) then 3 else 2)
    by_cases h0 : k = 0
    · subst h0
      have hn1 : (0:ℕ) ≠ n - 1 := by omega
      have hf : Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (0 = 0 ∨ pnat p (0 - 1) < pnat p 0) ∧
          (0 = n - 1 ∨ pnat p 0 > pnat p (0 + 1))) =
          Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p ⟨1, ngt1⟩ : ℕ) < p ⟨0, hk⟩) := by
        apply Finset.filter_congr
        intro p _
        simp only [eq_self_iff_true, true_or, true_and, hn1, false_or, zero_add]
        rw [hP p 0 hk, hP p 1 ngt1]
      rw [hf]
      have := hpair ⟨0, hk⟩ ⟨1, ngt1⟩ (by simp [Fin.ext_iff])
      simp only [eq_self_iff_true, true_or, if_true]
      omega
    by_cases hl : k = n - 1
    · subst hl
      have hn0 : n - 1 ≠ 0 := by omega
      have hf : Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (n - 1 = 0 ∨ pnat p (n - 1 - 1) < pnat p (n - 1)) ∧
          (n - 1 = n - 1 ∨ pnat p (n - 1) > pnat p (n - 1 + 1))) =
          Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (p ⟨n - 1 - 1, by omega⟩ : ℕ) < p ⟨n - 1, hk⟩) := by
        apply Finset.filter_congr
        intro p _
        simp only [eq_self_iff_true, true_or, and_true, hn0, false_or]
        rw [hP p (n - 1 - 1) (by omega), hP p (n - 1) hk]
      rw [hf]
      have := hpair ⟨n - 1, hk⟩ ⟨n - 1 - 1, by omega⟩ (by simp only [ne_eq, Fin.mk.injEq]; omega)
      simp only [eq_self_iff_true, or_true, if_true]
      omega
    · have hf : Finset.univ.filter (fun p : Equiv.Perm (Fin n) => (k = 0 ∨ pnat p (k - 1) < pnat p k) ∧
          (k = n - 1 ∨ pnat p k > pnat p (k + 1))) =
          Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
            (p ⟨k - 1, by omega⟩ : ℕ) < p ⟨k, hk⟩ ∧ (p ⟨k + 1, by omega⟩ : ℕ) < p ⟨k, hk⟩) := by
        apply Finset.filter_congr
        intro p _
        simp only [h0, hl, false_or, gt_iff_lt]
        rw [hP p (k - 1) (by omega), hP p k hk, hP p (k + 1) (by omega)]
      rw [hf]
      have := htri ⟨k, hk⟩ ⟨k - 1, by omega⟩ ⟨k + 1, by omega⟩
        (by simp only [ne_eq, Fin.mk.injEq]; omega) (by simp only [ne_eq, Fin.mk.injEq]; omega)
        (by simp only [ne_eq, Fin.mk.injEq]; omega)
      rw [if_neg (show ¬ (k = 0 ∨ k = n - 1) by omega)]
      omega
  have hw : ∑ i ∈ Finset.range n, (if (i = 0 ∨ i = n - 1) then 3 else 2) = 2 * n + 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h2 : ∑ i ∈ Finset.range m, (if (i + 1 = 0 ∨ i + 1 = m + 2 - 1) then 3 else 2) =
        ∑ i ∈ Finset.range m, 2 :=
      Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_range] at hi
        exact if_neg (show ¬ (i + 1 = 0 ∨ i + 1 = m + 2 - 1) by omega))
    have e0 : (if (0 = 0 ∨ 0 = m + 2 - 1) then 3 else 2) = 3 := if_pos (Or.inl rfl)
    have e1 : (if (m + 1 = 0 ∨ m + 1 = m + 2 - 1) then 3 else 2) = 3 :=
      if_pos (Or.inr (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ', h2, e0, e1]
    simp
    ring
  have hT : 6 * ∑ p : Equiv.Perm (Fin n), pcount p = n.factorial * (2 * n + 2) := by
    rw [hsum, Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hper k), ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun i => if (i = 0 ∨ i = n - 1) then 3 else 2) n, hw]
  have hn : ({p : Equiv.Perm (Fin n) | true = true}).ncard = n.factorial := by
    simp [Set.ncard_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hn]
  simp only [putnam_2006_a4_solution]
  have hX : (0:ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hTR : (6:ℝ) * ((∑ p : Equiv.Perm (Fin n), pcount p : ℕ) : ℝ) = ((n.factorial : ℕ) : ℝ) * (2 * (n : ℝ) + 2) := by
    exact_mod_cast hT
  rw [div_eq_iff hX.ne']
  linear_combination hTR / 6
