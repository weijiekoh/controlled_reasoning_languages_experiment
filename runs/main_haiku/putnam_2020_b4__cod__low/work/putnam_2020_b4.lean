import Mathlib

open Filter Topology Set

noncomputable abbrev putnam_2020_b4_solution : ℝ := 1 / 4040

def Vs (N : ℕ) : Set (ℕ → ℤ) :=
  {s | s 0 = 0 ∧ (∀ j ≥ N, s j = 0) ∧ (∀ j ∈ Icc 1 N, |s j - s (j - 1)| = 1)}

noncomputable def rot (N k : ℕ) (s : ℕ → ℤ) (j : ℕ) : ℤ :=
  if j ≤ N then s ((j + k) % N) - s (k % N) else 0

noncomputable def qf (N : ℕ) (s : ℕ → ℤ) : ℝ :=
  1 + ∑ j ∈ Finset.Icc 1 (N - 1), (3:ℝ) ^ (s j)

lemma sum_rot (g : ℕ → ℝ) (N : ℕ) (hN : 0 < N) (k : ℕ) :
    ∑ j ∈ Finset.range N, g ((j + k) % N) = ∑ j ∈ Finset.range N, g j := by
  induction k with
  | zero =>
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    simp [Nat.mod_eq_of_lt hj]
  | succ k ih =>
    have h1 : ∀ j, (j + (k + 1)) % N = ((j + 1) + k) % N := fun j => by
      rw [show j + (k + 1) = (j + 1) + k by ring]
    have h4 : (N + k) % N = (0 + k) % N := by simp [Nat.add_mod_left]
    have ha := Finset.sum_range_succ' (fun j => g ((j + k) % N)) N
    have hb := Finset.sum_range_succ (fun j => g ((j + k) % N)) N
    have hf : g ((N + k) % N) = g ((0 + k) % N) := by rw [h4]
    beta_reduce at ha hb
    have key : ∑ i ∈ Finset.range N, g ((i + 1 + k) % N)
        = ∑ i ∈ Finset.range N, g ((i + k) % N) := by linarith
    simp only [h1]
    rw [key, ih]

lemma Vs_finite (N : ℕ) : (Vs N).Finite := by
  have hB : (Set.pi (Set.univ : Set (Fin (N+1))) (fun _ => Set.Icc (-(N:ℤ)) N)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  refine Set.Finite.of_finite_image (f := fun s : ℕ → ℤ => fun i : Fin (N+1) => s i) ?_ ?_
  · refine hB.subset ?_
    rintro _ ⟨s, hs, rfl⟩
    simp only [Vs, Set.mem_setOf_eq] at hs
    obtain ⟨h0, hbig, hst⟩ := hs
    have hb : ∀ j, j ≤ N → |s j| ≤ j := by
      intro j
      induction j with
      | zero => intro _; simp [h0]
      | succ j ih =>
        intro hj
        have h1 := hst (j+1) ⟨by omega, hj⟩
        have h2 := abs_sub_abs_le_abs_sub (s (j+1)) (s j)
        have h3 := ih (by omega)
        simp only [Nat.add_sub_cancel] at h1
        push_cast
        linarith
    rw [Set.mem_pi]
    intro i _
    have h := hb i.1 (by omega)
    have h' := abs_le.mp h
    simp only [Set.mem_Icc]
    constructor <;> omega
  · intro s hs s' hs' hEq
    simp only [Vs, Set.mem_setOf_eq] at hs hs'
    obtain ⟨h0, hbig, _⟩ := hs
    obtain ⟨h0', hbig', _⟩ := hs'
    funext j
    by_cases hj : j ≤ N
    · have := congrFun hEq ⟨j, by omega⟩
      simpa using this
    · rw [hbig j (by omega), hbig' j (by omega)]

lemma step_mod (N : ℕ) (hN : 0 < N) (s : ℕ → ℤ) (hs : s ∈ Vs N) (a : ℕ) :
    |s ((a + 1) % N) - s (a % N)| = 1 := by
  simp only [Vs, Set.mem_setOf_eq] at hs
  obtain ⟨h0, hbig, hst⟩ := hs
  have hr := Nat.mod_lt a hN
  rw [← Nat.mod_add_mod a N 1]
  by_cases h : a % N + 1 < N
  · rw [Nat.mod_eq_of_lt h]
    have := hst (a % N + 1) ⟨by omega, by omega⟩
    simpa using this
  · have heq : a % N + 1 = N := by omega
    rw [heq, Nat.mod_self, h0]
    have := hst N ⟨by omega, le_refl N⟩
    rw [hbig N le_rfl] at this
    have hN1 : N - 1 = a % N := by omega
    rw [hN1] at this
    simpa using this

lemma rot_mem (N : ℕ) (hN : 0 < N) (k : ℕ) (s : ℕ → ℤ) (hs : s ∈ Vs N) :
    rot N k s ∈ Vs N := by
  have hs' := hs
  simp only [Vs, Set.mem_setOf_eq] at hs'
  obtain ⟨h0, hbig, hst⟩ := hs'
  simp only [Vs, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [rot, if_pos (by omega), Nat.zero_add, sub_self]
  · intro j hj
    by_cases h : j ≤ N
    · have hjN : j = N := by omega
      rw [rot, if_pos h, hjN, Nat.add_mod_left, sub_self]
    · rw [rot, if_neg h]
  · intro j hj
    simp only [Set.mem_Icc] at hj
    obtain ⟨hj1, hjN⟩ := hj
    have hA : rot N k s j = s ((j + k) % N) - s (k % N) := by rw [rot, if_pos hjN]
    have hB : rot N k s (j - 1) = s ((j - 1 + k) % N) - s (k % N) := by
      rw [rot, if_pos (by omega)]
    rw [hA, hB]
    have e : j + k = (j - 1 + k) + 1 := by omega
    rw [e]
    rw [show s ((j - 1 + k + 1) % N) - s (k % N) - (s ((j - 1 + k) % N) - s (k % N))
        = s ((j - 1 + k + 1) % N) - s ((j - 1 + k) % N) by ring]
    exact step_mod N hN s hs (j - 1 + k)

lemma rot_inv (N : ℕ) (hN : 0 < N) (a b : ℕ) (hab : (a + b) % N = 0) (s : ℕ → ℤ)
    (hs : s ∈ Vs N) : rot N a (rot N b s) = s := by
  have hs' := hs
  simp only [Vs, Set.mem_setOf_eq] at hs'
  obtain ⟨h0, hbig, _⟩ := hs'
  funext j
  by_cases hj : j ≤ N
  · have h1 : (j + a) % N ≤ N := (Nat.mod_lt _ hN).le
    have h2 : a % N ≤ N := (Nat.mod_lt _ hN).le
    have e1 : (j + a + b) % N = j % N := by
      rw [add_assoc, Nat.add_mod, hab, add_zero, Nat.mod_mod]
    have hsj : s (j % N) = s j := by
      rcases lt_or_eq_of_le hj with h | h
      · rw [Nat.mod_eq_of_lt h]
      · rw [h, Nat.mod_self, h0, hbig N le_rfl]
    simp only [rot, if_pos hj, if_pos h1, if_pos h2]
    rw [Nat.mod_add_mod, Nat.mod_add_mod, e1, hab, h0, hsj]
    ring
  · simp only [rot, if_neg hj]
    exact (hbig j (by omega)).symm

lemma mod_inv (N k : ℕ) (hN : 0 < N) : (k + (N - k % N)) % N = 0 := by
  have e : k % N + (N - k % N) = N := by have := Nat.mod_lt k hN; omega
  rw [← Nat.mod_add_mod k N (N - k % N), e, Nat.mod_self]

lemma inv_qf_rot (N : ℕ) (hN : 0 < N) (s : ℕ → ℤ) (hs : s ∈ Vs N) (k : ℕ) :
    1 / qf N (rot N k s) = (3:ℝ) ^ (s (k % N)) / ∑ i ∈ Finset.range N, (3:ℝ) ^ (s i) := by
  have hc : (3:ℝ) ^ (s (k % N)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hsplit : ∀ f : ℕ → ℝ, ∑ j ∈ Finset.Icc 1 (N - 1), f j = ∑ i ∈ Finset.range N, f i - f 0 := by
    intro f
    have hI : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
      ext x; simp; omega
    rw [hI, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
    simp only [zero_add]
    ring
  have hq : qf N (rot N k s) = (∑ i ∈ Finset.range N, (3:ℝ) ^ (s i)) / (3:ℝ) ^ (s (k % N)) := by
    unfold qf
    have hcongr : ∑ j ∈ Finset.Icc 1 (N - 1), (3:ℝ) ^ (rot N k s j)
        = ∑ j ∈ Finset.Icc 1 (N - 1), (3:ℝ) ^ (s ((j + k) % N)) / (3:ℝ) ^ (s (k % N)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have hjN : j ≤ N := by omega
      rw [rot, if_pos hjN, zpow_sub₀ (by norm_num)]
    rw [hcongr, ← Finset.sum_div]
    have hs2 := hsplit (fun j => (3:ℝ) ^ (s ((j + k) % N)))
    simp only [zero_add] at hs2
    rw [hs2]
    have hr := sum_rot (fun i => (3:ℝ) ^ (s i)) N hN k
    rw [hr, sub_div, div_self hc]
    ring
  rw [hq, one_div_div]

lemma sum_inv_rot (N : ℕ) (hN : 0 < N) (s : ℕ → ℤ) (hs : s ∈ Vs N) :
    ∑ k ∈ Finset.range N, 1 / qf N (rot N k s) = 1 := by
  have hS : (∑ i ∈ Finset.range N, (3:ℝ) ^ (s i)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.sum_pos
    · intro i _; positivity
    · exact ⟨0, Finset.mem_range.mpr hN⟩
  rw [Finset.sum_congr rfl (fun k _ => inv_qf_rot N hN s hs k), ← Finset.sum_div]
  have : ∑ k ∈ Finset.range N, (3:ℝ) ^ (s (k % N)) = ∑ i ∈ Finset.range N, (3:ℝ) ^ (s i) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
  rw [this, div_self hS]

lemma general (n : ℕ) (hn : 0 < n) :
    (∑' v : Vs (2 * n), 1 / qf (2 * n) v) / ((Vs (2 * n)).ncard : ℝ)
      = 1 / ((2 * n : ℕ) : ℝ) := by
  have hN : 0 < 2 * n := by omega
  have hfin := Vs_finite (2 * n)
  set N := 2 * n with hNdef
  set F := hfin.toFinset with hFdef
  have hF : ∀ v, v ∈ F ↔ v ∈ Vs N := fun v => hfin.mem_toFinset
  have hset : Vs N = ↑F := (Set.Finite.coe_toFinset hfin).symm
  have hcard : (Vs N).ncard = F.card := Set.ncard_eq_toFinset_card _ hfin
  have hbij : ∀ k, ∑ v ∈ F, 1 / qf N (rot N k v) = ∑ v ∈ F, 1 / qf N v := by
    intro k
    apply Finset.sum_nbij' (rot N k) (rot N (N - k % N))
    · intro a ha; exact (hF _).mpr (rot_mem N hN k a ((hF a).mp ha))
    · intro a ha; exact (hF _).mpr (rot_mem N hN _ a ((hF a).mp ha))
    · intro a ha
      exact rot_inv N hN _ _ (by rw [Nat.add_comm]; exact mod_inv N k hN) a ((hF a).mp ha)
    · intro a ha
      exact rot_inv N hN _ _ (mod_inv N k hN) a ((hF a).mp ha)
    · intro a ha; rfl
  have hsum1 : ∑ v ∈ F, ∑ k ∈ Finset.range N, 1 / qf N (rot N k v) = (F.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun v hv => sum_inv_rot N hN v ((hF v).mp hv))]
    simp
  rw [Finset.sum_comm] at hsum1
  simp only [hbij, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum1
  have htsum : ∑' v : Vs N, 1 / qf N v = ∑ v ∈ F, 1 / qf N v := by
    rw [hset]
    exact Finset.tsum_subtype' F (fun v => 1 / qf N v)
  have hw : (fun j : ℕ => if j < N ∧ j % 2 = 1 then (1:ℤ) else 0) ∈ Vs N := by
    simp only [Vs, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · simp
    · intro j hj
      rw [if_neg (by omega)]
    · intro j hj
      simp only [Set.mem_Icc] at hj
      split_ifs with h1 h2 <;> norm_num <;> omega
  have hFne : F.card ≠ 0 := by
    exact Finset.card_ne_zero.mpr ⟨_, (hF _).mpr hw⟩
  have hpos : (F.card : ℝ) ≠ 0 := by exact_mod_cast hFne
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hT : (∑ v ∈ F, 1 / qf N v) ≠ 0 := by
    intro h; apply hpos; rw [← hsum1, h, mul_zero]
  rw [htsum, hcard, ← hsum1]
  field_simp

/--
Let $n$ be a positive integer, and let $V_n$ be the set of integer $(2n+1)$-tuples $\mathbf{v} = (s_0, s_1, \cdots, s_{2n-1}, s_{2n})$ for which $s_0 = s_{2n} = 0$ and $|s_j - s_{j-1}| = 1$ for $j=1,2,\cdots,2n$. Define \[ q(\mathbf{v}) = 1 + \sum_{j=1}^{2n-1} 3^{s_j}, \] and let $M(n)$ be the average of $rac{1}{q(\mathbf{v})}$ over all $\mathbf{v} \in V_n$. Evaluate $M(2020)$.
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
  have key := general 2020 (by norm_num)
  show (∑' v : Vs (2 * 2020), 1 / qf (2 * 2020) v) / ((Vs (2 * 2020)).ncard : ℝ) = putnam_2020_b4_solution
  rw [key]
  norm_num [putnam_2020_b4_solution]
