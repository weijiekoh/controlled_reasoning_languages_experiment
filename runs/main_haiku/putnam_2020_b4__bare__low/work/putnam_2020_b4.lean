import Mathlib

open Filter Topology Set

noncomputable abbrev putnam_2020_b4_solution : ℝ := 1 / 4040

def pidx (M k j : ℕ) : ℕ := if k + j < M then k + j else k + j - M

def prot (n k : ℕ) (s : ℕ → ℤ) : ℕ → ℤ :=
  fun j => if j < 2 * n then s (pidx (2 * n) k j) - s k else 0

def PV (n : ℕ) : Set (ℕ → ℤ) :=
  {s : ℕ → ℤ | s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧ (∀ j ∈ Icc 1 (2 * n), |s j - s (j - 1)| = 1)}

noncomputable def PQ (n : ℕ) (s : ℕ → ℤ) : ℝ := 1 + ∑ j ∈ Finset.Icc 1 (2 * n - 1), (3:ℝ) ^ (s j)

lemma pidx_lt_of (M k j : ℕ) (hk : k < M) (hj : j < M) : pidx M k j < M := by
  unfold pidx; split_ifs with h <;> omega

lemma pidx_zero (M k : ℕ) (hk : k < M) : pidx M k 0 = k := by
  unfold pidx; split_ifs with h <;> omega

lemma pidx_surj (M k i : ℕ) (hk : k < M) (hi : i < M) : ∃ j, j < M ∧ pidx M k j = i := by
  by_cases h : k ≤ i
  · exact ⟨i - k, by omega, by unfold pidx; split_ifs <;> omega⟩
  · exact ⟨i + M - k, by omega, by unfold pidx; split_ifs <;> omega⟩

lemma perm_sum (M k : ℕ) (hk : k < M) (G : ℕ → ℝ) :
    ∑ j ∈ Finset.range M, G (pidx M k j) = ∑ i ∈ Finset.range M, G i := by
  obtain ⟨d, rfl⟩ : ∃ d, M = k + d := ⟨M - k, by omega⟩
  have h1 : ∑ j ∈ Finset.range (k + d), G (pidx (k + d) k j)
      = ∑ x ∈ Finset.range d, G (k + x) + ∑ x ∈ Finset.range k, G x := by
    rw [show k + d = d + k from add_comm _ _, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show pidx (d + k) k x = k + x by unfold pidx; split_ifs <;> omega]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show pidx (d + k) k (d + x) = x by unfold pidx; split_ifs <;> omega]
  rw [h1, Finset.sum_range_add, add_comm]

lemma sumsplit (M : ℕ) (hM : 0 < M) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range M, f j = f 0 + ∑ j ∈ Finset.Icc 1 (M - 1), f j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM]
  have : Finset.Ico (0 + 1) M = Finset.Icc 1 (M - 1) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [this]

lemma prot_zero (n k : ℕ) (s : ℕ → ℤ) (hk : k < 2 * n) : prot n k s 0 = 0 := by
  unfold prot
  rw [if_pos (by omega), pidx_zero _ _ hk, sub_self]

lemma prot_lt (n k : ℕ) (s : ℕ → ℤ) (j : ℕ) (hj : j < 2 * n) :
    prot n k s j = s (pidx (2 * n) k j) - s k := by
  unfold prot; rw [if_pos hj]

lemma prot_ge (n k : ℕ) (s : ℕ → ℤ) (j : ℕ) (hj : 2 * n ≤ j) : prot n k s j = 0 := by
  unfold prot; rw [if_neg (by omega)]

lemma cyc_adj (n : ℕ) (s : ℕ → ℤ) (hs : s ∈ PV n) (hn : 0 < n) (a b : ℕ)
    (ha : a < 2 * n) (hb : b < 2 * n)
    (h : a = b + 1 ∨ (a = 0 ∧ b = 2 * n - 1)) : |s a - s b| = 1 := by
  obtain ⟨h0, hz, hst⟩ := hs
  rcases h with h | ⟨rfl, rfl⟩
  · subst h
    have := hst (b + 1) ⟨by omega, by omega⟩
    simpa using this
  · have e := hst (2 * n) ⟨by omega, le_refl _⟩
    rw [hz (2 * n) le_rfl] at e
    rw [h0]
    exact e

lemma prot_mem (n k : ℕ) (hn : 0 < n) (hk : k < 2 * n) (s : ℕ → ℤ) (hs : s ∈ PV n) :
    prot n k s ∈ PV n := by
  have hs' := hs
  obtain ⟨h0, hz, hst⟩ := hs'
  refine ⟨prot_zero n k s hk, fun j hj => prot_ge n k s j hj, ?_⟩
  intro j hj
  obtain ⟨hj1, hj2⟩ := hj
  rcases Nat.lt_or_ge j (2 * n) with hlt | hge
  · rw [prot_lt n k s j hlt, prot_lt n k s (j - 1) (by omega)]
    have h := cyc_adj n s hs hn (pidx (2 * n) k j) (pidx (2 * n) k (j - 1))
      (pidx_lt_of (2 * n) k j hk hlt) (pidx_lt_of (2 * n) k (j - 1) hk (by omega))
      (by unfold pidx; split_ifs <;> omega)
    rw [show (s (pidx (2 * n) k j) - s k) - (s (pidx (2 * n) k (j - 1)) - s k)
        = s (pidx (2 * n) k j) - s (pidx (2 * n) k (j - 1)) by ring]
    exact h
  · have hj' : j = 2 * n := by omega
    subst hj'
    rw [prot_ge n k s (2 * n) le_rfl, prot_lt n k s (2 * n - 1) (by omega)]
    have h := cyc_adj n s hs hn k (pidx (2 * n) k (2 * n - 1)) hk
      (pidx_lt_of (2 * n) k (2 * n - 1) hk (by omega)) (by unfold pidx; split_ifs <;> omega)
    rw [zero_sub, abs_neg, abs_sub_comm]
    exact h

lemma prot_inj (n k : ℕ) (hk : k < 2 * n) (s t : ℕ → ℤ) (hs : s ∈ PV n) (ht : t ∈ PV n)
    (h : prot n k s = prot n k t) : s = t := by
  have hs0 : s 0 = 0 := hs.1
  have ht0 : t 0 = 0 := ht.1
  have key : ∀ i, i < 2 * n → s i = t i := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := pidx_surj (2 * n) k i hk hi
    obtain ⟨j0, hj0, hj00⟩ := pidx_surj (2 * n) k 0 hk (by omega)
    have e1 := congrFun h j
    have e2 := congrFun h j0
    rw [prot_lt n k s j hj, prot_lt n k t j hj, hji] at e1
    rw [prot_lt n k s j0 hj0, prot_lt n k t j0 hj0, hj00] at e2
    rw [hs0, ht0] at e2
    linarith
  funext i
  by_cases hi : i < 2 * n
  · exact key i hi
  · rw [hs.2.1 i (by omega), ht.2.1 i (by omega)]

lemma PV_bound (n : ℕ) (s : ℕ → ℤ) (hs : s ∈ PV n) (j : ℕ) : |s j| ≤ j := by
  obtain ⟨h0, hz, hst⟩ := hs
  induction j with
  | zero => simp [h0]
  | succ j ih =>
    by_cases hj : j + 1 ≤ 2 * n
    · have h1 := hst (j + 1) ⟨by omega, hj⟩
      simp only [Nat.add_sub_cancel] at h1
      have h2 : |s (j + 1)| ≤ |s (j + 1) - s j| + |s j| := by
        simpa using abs_add_le (s (j + 1) - s j) (s j)
      rw [h1] at h2
      push_cast
      linarith
    · rw [hz (j + 1) (by omega)]
      simp only [abs_zero]
      push_cast
      positivity

lemma PV_finite (n : ℕ) : (PV n).Finite := by
  have hfin : ((fun t : Fin (2 * n + 1) → ℤ => fun j : ℕ =>
      if h : j < 2 * n + 1 then t ⟨j, h⟩ else 0) ''
      (Set.pi Set.univ fun _ => Set.Icc (-(2 * n : ℤ)) (2 * n))).Finite :=
    Set.Finite.image _ (Set.Finite.pi fun _ => Set.finite_Icc _ _)
  refine hfin.subset ?_
  intro s hs
  refine ⟨fun i : Fin (2 * n + 1) => s i, ?_, ?_⟩
  · intro i _
    have hi : ((i : ℕ) : ℤ) ≤ 2 * n := by have := i.isLt; omega
    have hb := abs_le.mp (le_trans (PV_bound n s hs i) hi)
    exact ⟨hb.1, hb.2⟩
  · funext j
    simp only
    split_ifs with h
    · rfl
    · exact (hs.2.1 j (by omega)).symm

lemma PV_nonempty (n : ℕ) (hn : 0 < n) : ∃ s, s ∈ PV n := by
  refine ⟨fun j => if j ≤ n then (j : ℤ) else if j < 2 * n then 2 * (n : ℤ) - j else 0, ?_, ?_, ?_⟩
  · simp
  · intro j hj
    simp only
    split_ifs <;> omega
  · intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    simp only
    rw [abs_eq (by norm_num)]
    split_ifs <;> omega

lemma main_eq (n : ℕ) (hn : 0 < n) :
    (∑' v : PV n, 1 / PQ n v) / ((PV n).ncard : ℝ) = 1 / (2 * (n : ℝ)) := by
  classical
  have hfin := PV_finite n
  have := hfin.fintype
  have hsum : ∑' v : PV n, 1 / PQ n v = ∑ v ∈ hfin.toFinset, 1 / PQ n v := by
    rw [tsum_fintype]
    exact (Finset.sum_subtype hfin.toFinset (p := fun x => x ∈ PV n)
      (fun x => hfin.mem_toFinset) (fun v => 1 / PQ n v)).symm
  have hcard : (PV n).ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  obtain ⟨p, hp⟩ := PV_nonempty n hn
  have hpos : 0 < hfin.toFinset.card := Finset.card_pos.mpr ⟨p, hfin.mem_toFinset.mpr hp⟩
  have key : ∀ s ∈ PV n, ∑ k ∈ Finset.range (2 * n), 1 / PQ n (prot n k s) = 1 := by
    intro s hs
    have hG : 0 < ∑ i ∈ Finset.range (2 * n), (3:ℝ) ^ (s i) :=
      Finset.sum_pos (fun i _ => by positivity) (Finset.nonempty_range_iff.mpr (by omega))
    have hq : ∀ k < 2 * n, PQ n (prot n k s)
        = (∑ i ∈ Finset.range (2 * n), (3:ℝ) ^ (s i)) / (3:ℝ) ^ (s k) := by
      intro k hk
      have h1 : ∑ j ∈ Finset.range (2 * n), (3:ℝ) ^ (prot n k s j) = PQ n (prot n k s) := by
        rw [sumsplit (2 * n) (by omega), prot_zero n k s hk]
        simp [PQ]
      have h2 : ∑ j ∈ Finset.range (2 * n), (3:ℝ) ^ (prot n k s j)
          = ∑ j ∈ Finset.range (2 * n), (3:ℝ) ^ (s (pidx (2 * n) k j) - s k) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [prot_lt n k s j (Finset.mem_range.mp hj)]
      rw [← h1, h2, perm_sum (2 * n) k hk (fun i => (3:ℝ) ^ (s i - s k))]
      simp only [zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0)]
      rw [← Finset.sum_div]
    have hh : ∀ k ∈ Finset.range (2 * n), 1 / PQ n (prot n k s)
        = (3:ℝ) ^ (s k) / (∑ i ∈ Finset.range (2 * n), (3:ℝ) ^ (s i)) :=
      fun k hk => by rw [hq k (Finset.mem_range.mp hk), one_div_div]
    rw [Finset.sum_congr rfl hh, ← Finset.sum_div]
    exact div_self hG.ne'
  have perm : ∀ k < 2 * n, ∑ v ∈ hfin.toFinset, 1 / PQ n (prot n k v)
      = ∑ v ∈ hfin.toFinset, 1 / PQ n v := by
    intro k hk
    have hinj : ∀ v ∈ hfin.toFinset, ∀ w ∈ hfin.toFinset, prot n k v = prot n k w → v = w :=
      fun v hv w hw h => prot_inj n k hk v w (hfin.mem_toFinset.mp hv) (hfin.mem_toFinset.mp hw) h
    have hinjOn : Set.InjOn (prot n k) (hfin.toFinset : Set (ℕ → ℤ)) :=
      fun v hv w hw h => hinj v hv w hw h
    have himg : hfin.toFinset.image (prot n k) = hfin.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact hfin.mem_toFinset.mpr (prot_mem n k hn hk v (hfin.mem_toFinset.mp hv))
      · exact (Finset.card_image_of_injOn hinjOn).ge
    calc ∑ v ∈ hfin.toFinset, 1 / PQ n (prot n k v)
        = ∑ w ∈ hfin.toFinset.image (prot n k), 1 / PQ n w :=
          (Finset.sum_image (f := fun w => 1 / PQ n w) (fun v hv w hw h => hinj v hv w hw h)).symm
      _ = ∑ w ∈ hfin.toFinset, 1 / PQ n w := by rw [himg]
  have hdouble : ∑ k ∈ Finset.range (2 * n), ∑ v ∈ hfin.toFinset, 1 / PQ n (prot n k v)
      = (hfin.toFinset.card : ℝ) := by
    rw [Finset.sum_comm]
    have hv1 : ∀ v ∈ hfin.toFinset, ∑ k ∈ Finset.range (2 * n), 1 / PQ n (prot n k v) = 1 :=
      fun v hv => key v (hfin.mem_toFinset.mp hv)
    rw [Finset.sum_congr rfl hv1]
    simp
  have hconst : ∑ k ∈ Finset.range (2 * n), ∑ v ∈ hfin.toFinset, 1 / PQ n (prot n k v)
      = (2 * n : ℝ) * ∑ v ∈ hfin.toFinset, 1 / PQ n v := by
    rw [Finset.sum_congr rfl (fun k hk => perm k (Finset.mem_range.mp hk))]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum, hcard]
  have hS : (hfin.toFinset.card : ℝ) = (2 * n : ℝ) * ∑ v ∈ hfin.toFinset, 1 / PQ n v := by
    rw [← hdouble, hconst]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (hfin.toFinset.card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [div_eq_div_iff hcR (by positivity)]
  linarith [hS]

/--
Let $n$ be a positive integer, and let $V_n$ be the set of integer $(2n+1)$-tuples $\mathbf{v} = (s_0, s_1, \cdots, s_{2n-1}, s_{2n})$ for which $s_0 = s_{2n} = 0$ and $|s_j - s_{j-1}| = 1$ for $j=1,2,\cdots,2n$. Define \[ q(\mathbf{v}) = 1 + \sum_{j=1}^{2n-1} 3^{s_j}, \] and let $M(n)$ be the average of $\frac{1}{q(\mathbf{v})}$ over all $\mathbf{v} \in V_n$. Evaluate $M(2020)$.
-/
theorem putnam_2020_b4
(V : ℕ → Set (ℕ → ℤ))
(q : ℕ → (ℕ → ℤ) → ℝ)
(M : ℕ → ℝ)
(hV : V = fun n ↦ ({s : ℕ → ℤ | s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧ (∀ j ∈ Icc 1 (2 * n), |s j - s (j - 1)| = 1)}))
(hq : q = fun n s ↦ 1 + ∑ j ∈ Finset.Icc 1 (2 * n - 1), 3 ^ (s j))
(hM : M = fun n ↦ (∑' v : V n, 1 / (q n v)) / (V n).ncard)
: (M 2020 = putnam_2020_b4_solution) := by

  subst hV hq hM
  show (∑' v : PV 2020, 1 / PQ 2020 v) / ((PV 2020).ncard : ℝ) = putnam_2020_b4_solution
  rw [main_eq 2020 (by norm_num)]
  norm_num [putnam_2020_b4_solution]
