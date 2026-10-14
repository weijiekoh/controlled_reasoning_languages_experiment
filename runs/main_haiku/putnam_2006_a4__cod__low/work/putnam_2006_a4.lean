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
  classical
  have hN : ({p : Equiv.Perm (Fin n) | true}.ncard) = n.factorial := by
    rw [show {p : Equiv.Perm (Fin n) | true = true} = Set.univ from by ext; simp]
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hone : ∑ _p : Equiv.Perm (Fin n), (1:ℕ) = n.factorial := by
    simp [Fintype.card_perm]
  have hswap : ∀ (Q : Equiv.Perm (Fin n) → ℕ) (τ : Equiv.Perm (Fin n)),
      ∑ p, Q (p * τ) = ∑ p, Q p :=
    fun Q τ => Equiv.sum_comp (Equiv.mulRight τ) Q
  have hne : ∀ a b : Fin n, a.1 ≠ b.1 → a ≠ b := fun a b h e => h (congrArg Fin.val e)
  have hpair : ∀ x y : Fin n, x ≠ y →
      2 * ∑ p : Equiv.Perm (Fin n), (if (p x : ℕ) < p y then 1 else 0) = n.factorial := by
    intro x y hxy
    have hB : ∑ p : Equiv.Perm (Fin n), (if (p y : ℕ) < p x then 1 else 0)
        = ∑ p : Equiv.Perm (Fin n), (if (p x : ℕ) < p y then 1 else 0) := by
      have := hswap (fun q : Equiv.Perm (Fin n) => if (q x : ℕ) < q y then 1 else 0) (Equiv.swap x y)
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at this
      exact this
    have hsum : ∑ p : Equiv.Perm (Fin n), ((if (p x : ℕ) < p y then 1 else 0)
        + (if (p y : ℕ) < p x then 1 else 0)) = ∑ _p : Equiv.Perm (Fin n), (1:ℕ) := by
      apply Finset.sum_congr rfl
      intro p _
      have hp : (p x : ℕ) ≠ p y := fun h => hxy (p.injective (Fin.ext h))
      split_ifs <;> omega
    rw [Finset.sum_add_distrib, hB, hone] at hsum
    omega
  have hTs1 : ∀ a b c : Fin n, a ≠ b → c ≠ a → c ≠ b →
      ∑ p : Equiv.Perm (Fin n), (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        = ∑ p : Equiv.Perm (Fin n), (if (p a : ℕ) < p b ∧ (p c : ℕ) < p b then 1 else 0) := by
    intro a b c hab hca hcb
    have := hswap (fun q : Equiv.Perm (Fin n) => if (q b : ℕ) < q a ∧ (q c : ℕ) < q a then 1 else 0)
      (Equiv.swap a b)
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hca hcb] at this
    exact this.symm
  have hTs2 : ∀ a b c : Fin n, a ≠ c → b ≠ a → b ≠ c →
      ∑ p : Equiv.Perm (Fin n), (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        = ∑ p : Equiv.Perm (Fin n), (if (p b : ℕ) < p c ∧ (p a : ℕ) < p c then 1 else 0) := by
    intro a b c hac hba hbc
    have := hswap (fun q : Equiv.Perm (Fin n) => if (q b : ℕ) < q a ∧ (q c : ℕ) < q a then 1 else 0)
      (Equiv.swap a c)
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hba hbc] at this
    exact this.symm
  have hpt3 : ∀ a b c : Fin n, a ≠ b → c ≠ a → c ≠ b → ∀ p : Equiv.Perm (Fin n),
      (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        + (if (p a : ℕ) < p b ∧ (p c : ℕ) < p b then 1 else 0)
        + (if (p b : ℕ) < p c ∧ (p a : ℕ) < p c then 1 else 0) = 1 := by
    intro a b c hab hca hcb p
    have h1 : (p a : ℕ) ≠ p b := fun h => hab (p.injective (Fin.ext h))
    have h2 : (p c : ℕ) ≠ p a := fun h => hca (p.injective (Fin.ext h))
    have h3 : (p c : ℕ) ≠ p b := fun h => hcb (p.injective (Fin.ext h))
    split_ifs <;> omega
  have htri : ∀ a b c : Fin n, a ≠ b → c ≠ a → c ≠ b →
      3 * ∑ p : Equiv.Perm (Fin n), (if (p b : ℕ) < p a ∧ (p c : ℕ) < p a then 1 else 0)
        = n.factorial := by
    intro a b c hab hca hcb
    have h1 := hTs1 a b c hab hca hcb
    have h2 := hTs2 a b c (Ne.symm hca) (Ne.symm hab) (Ne.symm hcb)
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun p (_ : p ∈ Finset.univ) => hpt3 a b c hab hca hcb p)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hone] at hs
    omega
  have hrange : ∀ (M n m : ℕ), n = m + 2 →
      ∑ i ∈ Finset.range n, (if i = 0 ∨ i = n - 1 then 3 * M else 2 * M) = 2 * M * (n + 1) := by
    intro M n m hn
    subst hn
    rw [show m + 2 - 1 = m + 1 by omega, Finset.sum_range_succ', Finset.sum_range_succ]
    have hmid : ∑ i ∈ Finset.range m, (if i + 1 = 0 ∨ i + 1 = m + 1 then 3 * M else 2 * M)
        = ∑ i ∈ Finset.range m, 2 * M :=
      Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_range] at hi
        rw [if_neg (by omega)])
    rw [hmid]
    simp [Finset.sum_const, Finset.card_range]
    ring
  have hS : ∀ p : Equiv.Perm (Fin n), pcount p = ∑ k : Fin n,
      (if ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
        then 1 else 0) := by
    intro p
    have h1 : {k : Fin n | (k.1 = 0 ∨ (pnat p) (k.1 - 1) < (pnat p) k.1)
        ∧ (k.1 = n - 1 ∨ (pnat p) k.1 > (pnat p) (k.1 + 1))}
        = ↑(Finset.univ.filter (fun k : Fin n => (k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1)
            ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))) := by
      ext k; simp
    have h2 := hpcount p
    rw [h1, Set.encard_coe_eq_coe_finsetCard, Finset.card_filter] at h2
    exact_mod_cast h2
  obtain ⟨g, hgd⟩ : ∃ g : Fin n → ℕ, ∀ k : Fin n, g k = ∑ p : Equiv.Perm (Fin n),
      (if ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
        then 1 else 0) := ⟨_, fun k => rfl⟩
  have hsum : ∑ p, pcount p = ∑ k : Fin n, g k := by
    rw [Finset.sum_congr rfl (fun p _ => hS p), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => (hgd k).symm)
  have hg : ∀ k : Fin n, 6 * g k
      = if (k.1 = 0 ∨ k.1 = n - 1) then 3 * n.factorial else 2 * n.factorial := by
    intro k
    rw [hgd k]
    by_cases h0 : k.1 = 0
    · have hn1 : k.1 ≠ n - 1 := by omega
      have hF : ∀ p : Equiv.Perm (Fin n),
          ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
            ↔ pnat p (k.1 + 1) < pnat p k.1 :=
        fun p => ⟨fun h => h.2.resolve_left hn1, fun h => ⟨Or.inl h0, Or.inr h⟩⟩
      obtain ⟨R, hRv⟩ : ∃ R : Fin n, R.1 = k.1 + 1 := ⟨⟨k.1 + 1, by omega⟩, rfl⟩
      have hR : ∀ p : Equiv.Perm (Fin n), pnat p (k.1 + 1) = (p R : ℕ) :=
        fun p => by rw [← hRv]; exact hpnat p R
      have hpr := hpair R k (hne _ _ (by omega))
      have heq : ∑ p : Equiv.Perm (Fin n),
          (if ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
            then 1 else 0)
          = ∑ p : Equiv.Perm (Fin n), (if (p R : ℕ) < p k then 1 else 0) := by
        simp only [hF]; simp only [hR, hpnat]
      rw [if_pos (Or.inl h0), heq]
      omega
    · by_cases h1 : k.1 = n - 1
      · obtain ⟨L, hLv⟩ : ∃ L : Fin n, L.1 = k.1 - 1 := ⟨⟨k.1 - 1, by omega⟩, rfl⟩
        have hL : ∀ p : Equiv.Perm (Fin n), pnat p (k.1 - 1) = (p L : ℕ) :=
          fun p => by rw [← hLv]; exact hpnat p L
        have hF : ∀ p : Equiv.Perm (Fin n),
            ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
              ↔ pnat p (k.1 - 1) < pnat p k.1 :=
          fun p => ⟨fun h => h.1.resolve_left h0, fun h => ⟨Or.inr h, Or.inl h1⟩⟩
        have hpr := hpair L k (hne _ _ (by omega))
        have heq : ∑ p : Equiv.Perm (Fin n),
            (if ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
              then 1 else 0)
            = ∑ p : Equiv.Perm (Fin n), (if (p L : ℕ) < p k then 1 else 0) := by
          simp only [hF]; simp only [hL, hpnat]
        rw [if_pos (Or.inr h1), heq]
        omega
      · obtain ⟨L, hLv⟩ : ∃ L : Fin n, L.1 = k.1 - 1 := ⟨⟨k.1 - 1, by omega⟩, rfl⟩
        obtain ⟨R, hRv⟩ : ∃ R : Fin n, R.1 = k.1 + 1 := ⟨⟨k.1 + 1, by omega⟩, rfl⟩
        have hL : ∀ p : Equiv.Perm (Fin n), pnat p (k.1 - 1) = (p L : ℕ) :=
          fun p => by rw [← hLv]; exact hpnat p L
        have hR : ∀ p : Equiv.Perm (Fin n), pnat p (k.1 + 1) = (p R : ℕ) :=
          fun p => by rw [← hRv]; exact hpnat p R
        have hF : ∀ p : Equiv.Perm (Fin n),
            ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
              ↔ (pnat p (k.1 - 1) < pnat p k.1 ∧ pnat p (k.1 + 1) < pnat p k.1) :=
          fun p => ⟨fun h => ⟨h.1.resolve_left h0, h.2.resolve_left h1⟩,
            fun h => ⟨Or.inr h.1, Or.inr h.2⟩⟩
        have ht := htri k L R (hne _ _ (by omega)) (hne _ _ (by omega)) (hne _ _ (by omega))
        have heq : ∑ p : Equiv.Perm (Fin n),
            (if ((k.1 = 0 ∨ pnat p (k.1 - 1) < pnat p k.1) ∧ (k.1 = n - 1 ∨ pnat p k.1 > pnat p (k.1 + 1)))
              then 1 else 0)
            = ∑ p : Equiv.Perm (Fin n), (if (p L : ℕ) < p k ∧ (p R : ℕ) < p k then 1 else 0) := by
          simp only [hF]; simp only [hL, hR, hpnat]
        rw [if_neg (by omega), heq]
        omega
  have h6 : 6 * ∑ p, pcount p
      = ∑ k : Fin n, (if (k.1 = 0 ∨ k.1 = n - 1) then 3 * n.factorial else 2 * n.factorial) := by
    rw [hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hg k)
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hfin := Fin.sum_univ_eq_sum_range
    (fun i => if i = 0 ∨ i = n - 1 then 3 * n.factorial else 2 * n.factorial) n
  rw [hfin, hrange (n.factorial) n m hm] at h6
  have hT : 3 * ∑ p, pcount p = n.factorial * (n + 1) := by linarith
  rw [hN]
  simp only [putnam_2006_a4_solution]
  have hfpos : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hTR : (3:ℝ) * ((∑ p, pcount p : ℕ) : ℝ) = (n.factorial : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast hT
  rw [div_eq_iff hfpos]
  linarith
