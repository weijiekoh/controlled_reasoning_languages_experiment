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

  have G : ∀ (σ : Equiv.Perm (Fin n)) (P Q : Equiv.Perm (Fin n) → Prop) [DecidablePred P] [DecidablePred Q],
      (∀ p, P p ↔ Q (p * σ)) →
      (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
    intro σ P Q _ _ h
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulRight σ) h)
  have fne : ∀ x y : Fin n, x.val ≠ y.val → x ≠ y := fun x y h e => h (congrArg Fin.val e)
  have Htrip : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c →
      3 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p a < p b ∧ p c < p b)).card
        = n.factorial := by
    intro a b c hab hac hbc
    have hca : c ≠ a := hac.symm
    have hcb : c ≠ b := hbc.symm
    have e1 := G (Equiv.swap a b) (fun p => p a < p b ∧ p c < p b)
      (fun p => p b < p a ∧ p c < p a)
      (fun p => by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hca, hcb])
    have e2 := G (Equiv.swap b c) (fun p => p a < p b ∧ p c < p b)
      (fun p => p a < p c ∧ p b < p c)
      (fun p => by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hab, hac])
    have hpt : ∀ p : Equiv.Perm (Fin n),
        ((if p a < p b ∧ p c < p b then 1 else 0) + (if p b < p a ∧ p c < p a then 1 else 0)
          + (if p a < p c ∧ p b < p c then 1 else 0) : ℕ) = 1 := by
      intro p
      have h1 : (p a).val ≠ (p b).val := fun h => hab (p.injective (Fin.ext h))
      have h2 : (p a).val ≠ (p c).val := fun h => hac (p.injective (Fin.ext h))
      have h3 : (p b).val ≠ (p c).val := fun h => hbc (p.injective (Fin.ext h))
      simp only [Fin.lt_def]
      split_ifs <;> omega
    have hs : (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p a < p b ∧ p c < p b)).card
        + (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p b < p a ∧ p c < p a)).card
        + (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p a < p c ∧ p b < p c)).card
        = n.factorial := by
      rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun p _ => hpt p)]
      simp [Fintype.card_perm]
    omega
  have Hend : ∀ a b : Fin n, a ≠ b →
      2 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p a < p b)).card = n.factorial := by
    intro a b hab
    have e := G (Equiv.swap a b) (fun p => p a < p b) (fun p => p b < p a)
      (fun p => by simp [Equiv.Perm.mul_apply])
    have hs : (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p a < p b)).card
        + (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p b < p a)).card = n.factorial := by
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun p _ => (by
          have h1 : (p a).val ≠ (p b).val := fun h => hab (p.injective (Fin.ext h))
          simp only [Fin.lt_def]
          split_ifs <;> omega : (if p a < p b then 1 else 0) + (if p b < p a then 1 else 0) = 1))]
      simp [Fintype.card_perm]
    omega
  have hkint : ∀ (p : Equiv.Perm (Fin n)) (k : Fin n) (h1 : 0 < k.val) (h2 : k.val < n - 1),
      ((k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
        (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))
      ↔ (p ⟨k.val - 1, by omega⟩ < p k ∧ p ⟨k.val + 1, by omega⟩ < p k) := by
    intro p k h1 h2
    have e1 : pnat p (k.val - 1) = (p ⟨k.val - 1, by omega⟩).val := hpnat p ⟨k.val - 1, by omega⟩
    have e2 : pnat p (k.val + 1) = (p ⟨k.val + 1, by omega⟩).val := hpnat p ⟨k.val + 1, by omega⟩
    have e3 : pnat p k.val = (p k).val := hpnat p k
    rw [e1, e2, e3]
    have h0 : k.val ≠ 0 := by omega
    have hn : k.val ≠ n - 1 := by omega
    simp [-Fin.val_fin_lt, h0, hn, Fin.lt_def]
  have hcard_end : ∀ k : Fin n, (k.val = 0 ∨ k.val = n - 1) →
      2 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
        (k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
        (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))).card = n.factorial := by
    intro k hk
    have hk0 : k.val ≠ 0 ∨ k.val = 0 := by omega
    rcases hk with hk | hk
    · have hj : k.val + 1 < n := by omega
      have hn : k.val ≠ n - 1 := by omega
      have e : ∀ p : Equiv.Perm (Fin n),
          ((k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
            (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))
          ↔ p ⟨k.val + 1, hj⟩ < p k := by
        intro p
        have e2 : pnat p (k.val + 1) = (p ⟨k.val + 1, hj⟩).val := hpnat p ⟨k.val + 1, hj⟩
        have e3 : pnat p k.val = (p k).val := hpnat p k
        rw [e2, e3]
        simp [-Fin.val_fin_lt, hk, show 0 ≠ n - 1 by omega, Fin.lt_def]
      have hne : (⟨k.val + 1, hj⟩ : Fin n) ≠ k := fne _ _ (by show k.val + 1 ≠ k.val; omega)
      have := Hend _ _ hne
      rw [Finset.filter_congr (fun p _ => e p)]
      exact this
    · have hi : k.val - 1 < n := by omega
      have hn0 : k.val ≠ 0 := by omega
      have e : ∀ p : Equiv.Perm (Fin n),
          ((k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
            (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))
          ↔ p ⟨k.val - 1, hi⟩ < p k := by
        intro p
        have e1 : pnat p (k.val - 1) = (p ⟨k.val - 1, hi⟩).val := hpnat p ⟨k.val - 1, hi⟩
        have e3 : pnat p k.val = (p k).val := hpnat p k
        rw [e1, e3]
        simp [-Fin.val_fin_lt, hk, show n - 1 ≠ 0 by omega, Fin.lt_def]
      have hne : (⟨k.val - 1, hi⟩ : Fin n) ≠ k := fne _ _ (by show k.val - 1 ≠ k.val; omega)
      have := Hend _ _ hne
      rw [Finset.filter_congr (fun p _ => e p)]
      exact this
  have hcard_int : ∀ k : Fin n, 0 < k.val → k.val < n - 1 →
      3 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
        (k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
        (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))).card = n.factorial := by
    intro k h1 h2
    rw [Finset.filter_congr (fun p _ => hkint p k h1 h2)]
    apply Htrip
    · exact fne _ _ (by show k.val - 1 ≠ k.val; omega)
    · exact fne _ _ (by show k.val - 1 ≠ k.val + 1; omega)
    · exact fne _ _ (by show k.val ≠ k.val + 1; omega)
  have h6 : ∀ k : Fin n, 6 * (Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
        (k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
        (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))).card
      = (if (k.val = 0 ∨ k.val = n - 1) then 3 * n.factorial else 2 * n.factorial) := by
    intro k
    have hlt := k.isLt
    split_ifs with hk
    · have := hcard_end k hk
      omega
    · have h1 : 0 < k.val := by omega
      have h2 : k.val < n - 1 := by omega
      have := hcard_int k h1 h2
      omega
  have hpc : ∀ p : Equiv.Perm (Fin n), pcount p =
      (Finset.univ.filter (fun k : Fin n =>
        (k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
        (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))).card := by
    intro p
    have h := hpcount p
    have hs : {k : Fin n | (k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
        (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1))}
        = ↑(Finset.univ.filter (fun k : Fin n =>
          (k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
          (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))) := by
      ext k; simp
    rw [hs, Set.encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  have hT : ∑ p, pcount p = ∑ k : Fin n, (Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
        (k.val = 0 ∨ pnat p (k.val - 1) < pnat p k.val) ∧
        (k.val = n - 1 ∨ pnat p k.val > pnat p (k.val + 1)))).card := by
    simp only [hpc, Finset.card_filter]
    exact Finset.sum_comm
  have hsumr : ∑ k : Fin n, (if (k.val = 0 ∨ k.val = n - 1) then 3 * n.factorial
      else 2 * n.factorial) = 2 * n.factorial * (n + 1) := by
    have hf := Fin.sum_univ_eq_sum_range
      (fun i => if (i = 0 ∨ i = n - 1) then 3 * n.factorial else 2 * n.factorial) n
    rw [hf]
    rw [Finset.sum_congr rfl (fun i _ => (show (if (i = 0 ∨ i = n - 1) then 3 * n.factorial
        else 2 * n.factorial) = 2 * n.factorial + (if i = 0 then n.factorial else 0)
        + (if i = n - 1 then n.factorial else 0) by split_ifs <;> omega))]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, show 0 < n by omega,
      show n - 1 < n by omega]
    ring
  have hT6 : 6 * (∑ p, pcount p) = 2 * n.factorial * (n + 1) := by
    rw [hT, Finset.mul_sum, ← hsumr]
    exact Finset.sum_congr rfl (fun k _ => h6 k)
  have hT3 : 3 * (∑ p, pcount p) = (n + 1) * n.factorial := by
    linarith
  have hncard : ({p : Equiv.Perm (Fin n) | true = true}).ncard = n.factorial := by
    simp [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hncard]
  simp only [putnam_2006_a4_solution]
  have hR : (3 : ℝ) * ((∑ p, pcount p : ℕ) : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    exact_mod_cast hT3
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [div_eq_iff hf]
  linarith
