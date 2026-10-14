import Mathlib

open Filter Topology Set

noncomputable abbrev putnam_2020_b4_solution : ℝ := 1 / 4040
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
  obtain ⟨rot, hrot⟩ : ∃ rot : ℕ → ℕ → (ℕ → ℤ) → (ℕ → ℤ),
      ∀ N k s j, rot N k s j = if j ≤ N then s ((k + j) % N) - s (k % N) else 0 :=
    ⟨fun N k s j => if j ≤ N then s ((k + j) % N) - s (k % N) else 0, fun _ _ _ _ => rfl⟩
  have rot_zero : ∀ N k (s : ℕ → ℤ), rot N k s 0 = 0 := by
    intro N k s
    rw [hrot, if_pos (Nat.zero_le _), add_zero, sub_self]
  have rot_rot : ∀ N a b (s : ℕ → ℤ), s 0 = 0 → (∀ j ≥ N, s j = 0) → (a + b) % N = 0 → 0 < N →
      rot N b (rot N a s) = s := by
    intro N a b s h0 hz hab hN
    funext j
    simp only [hrot]
    by_cases hj : j ≤ N
    · have h1 : (b + j) % N ≤ N := (Nat.mod_lt _ hN).le
      have h2 : b % N ≤ N := (Nat.mod_lt _ hN).le
      rw [if_pos hj, if_pos h1, if_pos h2]
      have e1 : (a + (b + j) % N) % N = j % N := by
        rw [Nat.add_mod_mod, show a + (b + j) = (a + b) + j by ring, Nat.add_mod, hab, zero_add,
          Nat.mod_mod]
      have e2 : (a + b % N) % N = 0 := by rw [Nat.add_mod_mod, hab]
      have e3 : s (j % N) = s j := by
        rcases Nat.lt_or_ge j N with h | h
        · rw [Nat.mod_eq_of_lt h]
        · have hjN : j = N := by omega
          rw [hjN, Nat.mod_self, h0, hz N le_rfl]
      rw [e1, e2, h0, e3]; ring
    · rw [if_neg hj, hz j (by omega)]
  have cyc : ∀ N (s : ℕ → ℤ), 0 < N → s 0 = 0 → (∀ j ≥ N, s j = 0) →
      (∀ j ∈ Set.Icc 1 N, |s j - s (j - 1)| = 1) → ∀ r < N, |s ((r + 1) % N) - s r| = 1 := by
    intro N s hN h0 hz hs r hr
    rcases Nat.lt_or_ge (r + 1) N with h | h
    · rw [Nat.mod_eq_of_lt h]
      have := hs (r + 1) (Set.mem_Icc.mpr ⟨by omega, h.le⟩)
      simpa using this
    · have hrN : r + 1 = N := by omega
      rw [hrN, Nat.mod_self, h0]
      have h2 := hs N (Set.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      have e : N - 1 = r := by omega
      rw [e, hz N le_rfl] at h2
      simpa using h2
  have rot_mem : ∀ N k (s : ℕ → ℤ), 0 < N → s 0 = 0 → (∀ j ≥ N, s j = 0) →
      (∀ j ∈ Set.Icc 1 N, |s j - s (j - 1)| = 1) →
      rot N k s 0 = 0 ∧ (∀ j ≥ N, rot N k s j = 0) ∧
        (∀ j ∈ Set.Icc 1 N, |rot N k s j - rot N k s (j - 1)| = 1) := by
    intro N k s hN h0 hz hs
    refine ⟨rot_zero N k s, ?_, ?_⟩
    · intro j hj
      rw [hrot]
      by_cases h : j ≤ N
      · have hjN : j = N := by omega
        rw [if_pos h, hjN, Nat.add_mod_right, sub_self]
      · rw [if_neg h]
    · intro j hj
      obtain ⟨hj1, hjN⟩ := Set.mem_Icc.mp hj
      have hc := cyc N s hN h0 hz hs
      rw [hrot, hrot, if_pos hjN, if_pos (show j - 1 ≤ N by omega)]
      have h3 := hc ((k + (j - 1)) % N) (Nat.mod_lt _ hN)
      rw [Nat.mod_add_mod] at h3
      have e : k + j = k + (j - 1) + 1 := by omega
      rw [e]
      have e2 : s ((k + (j - 1) + 1) % N) - s (k % N) - (s ((k + (j - 1)) % N) - s (k % N))
          = s ((k + (j - 1) + 1) % N) - s ((k + (j - 1)) % N) := by ring
      rw [e2]; exact h3
  have per_sum : ∀ (N : ℕ) (h : ℕ → ℝ), (∀ i, h (i + N) = h i) →
      ∀ k, ∑ i ∈ Finset.range N, h (k + i) = ∑ i ∈ Finset.range N, h i := by
    intro N h hp k
    induction k with
    | zero => simp
    | succ k ih =>
      have a := Finset.sum_range_succ' (fun i => h (k + i)) N
      have b := Finset.sum_range_succ (fun i => h (k + i)) N
      have c := hp k
      have d : ∑ i ∈ Finset.range N, h (k + 1 + i) = ∑ i ∈ Finset.range N, h (k + (i + 1)) := by
        apply Finset.sum_congr rfl; intro i _; congr 1; omega
      simp only [add_zero] at a b
      rw [d]
      linarith
  have qA : ∀ N k (s : ℕ → ℤ), 0 < N →
      1 + ∑ j ∈ Finset.Icc 1 (N - 1), (3:ℝ) ^ (rot N k s j)
        = (∑ i ∈ Finset.range N, (3:ℝ) ^ (s i)) * (3:ℝ) ^ (-(s (k % N))) := by
    intro N k s hN
    have e : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have step1 : ∑ j ∈ Finset.Icc 1 (N - 1), (3:ℝ) ^ (rot N k s j)
        = ∑ i ∈ Finset.range N, (3:ℝ) ^ (rot N k s i) - 1 := by
      rw [e, Finset.sum_Ico_eq_sub _ (show 1 ≤ N by omega), Finset.sum_range_one, rot_zero,
        zpow_zero]
    have step2 : ∑ i ∈ Finset.range N, (3:ℝ) ^ (rot N k s i)
        = (∑ i ∈ Finset.range N, (3:ℝ) ^ (s i)) * (3:ℝ) ^ (-(s (k % N))) := by
      have h1 : ∀ i ∈ Finset.range N, (3:ℝ) ^ (rot N k s i)
          = (3:ℝ) ^ (s ((k + i) % N)) * (3:ℝ) ^ (-(s (k % N))) := by
        intro i hi
        have hi' : i < N := Finset.mem_range.mp hi
        rw [hrot, if_pos hi'.le, sub_eq_add_neg, zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
      congr 1
      have hk : ∑ i ∈ Finset.range N, (3:ℝ) ^ (s ((k + i) % N))
          = ∑ i ∈ Finset.range N, (3:ℝ) ^ (s (i % N)) :=
        per_sum N (fun i => (3:ℝ) ^ (s (i % N))) (by intro i; simp [Nat.add_mod_right]) k
      rw [hk]
      exact Finset.sum_congr rfl (fun i hi => by rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi)])
    rw [step1, step2]; ring
  have Bl : ∀ N (s : ℕ → ℤ), 0 < N →
      ∑ k ∈ Finset.range N, 1 / (1 + ∑ j ∈ Finset.Icc 1 (N - 1), (3:ℝ) ^ (rot N k s j)) = 1 := by
    intro N s hN
    have hT : 0 < ∑ i ∈ Finset.range N, (3:ℝ) ^ (s i) :=
      Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.mpr hN⟩
    have hT' := hT.ne'
    have hk : ∀ k ∈ Finset.range N,
        1 / (1 + ∑ j ∈ Finset.Icc 1 (N - 1), (3:ℝ) ^ (rot N k s j))
          = (3:ℝ) ^ (s (k % N)) / ∑ i ∈ Finset.range N, (3:ℝ) ^ (s i) := by
      intro k _
      have h3 : (3:ℝ) ^ (s (k % N)) ≠ 0 := zpow_ne_zero _ (by norm_num)
      rw [qA N k s hN, zpow_neg]
      field_simp
    rw [Finset.sum_congr rfl hk, ← Finset.sum_div]
    rw [show ∑ k ∈ Finset.range N, (3:ℝ) ^ (s (k % N)) = ∑ i ∈ Finset.range N, (3:ℝ) ^ (s i) from
      Finset.sum_congr rfl (fun k hk => by rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk)])]
    exact div_self hT'
  have finP : ∀ N : ℕ, {s : ℕ → ℤ | s 0 = 0 ∧ (∀ j ≥ N, s j = 0) ∧
      (∀ j ∈ Set.Icc 1 N, |s j - s (j - 1)| = 1)}.Finite := by
    intro N
    have hB : (Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (-(N:ℤ)) N)).Finite :=
      Set.Finite.pi (fun _ => Set.finite_Icc _ _)
    refine (hB.image (fun g : Fin (N + 1) → ℤ => fun j : ℕ =>
      if h : j < N + 1 then g ⟨j, h⟩ else 0)).subset ?_
    intro s hs
    obtain ⟨h0, hz, hst⟩ := hs
    have bd : ∀ j, j ≤ N → |s j| ≤ (j : ℤ) := by
      intro j
      induction j with
      | zero => intro _; simp [h0]
      | succ j ih =>
        intro hj
        have h1 := hst (j + 1) (Set.mem_Icc.mpr ⟨by omega, hj⟩)
        have e : j + 1 - 1 = j := by omega
        rw [e, abs_eq (by norm_num : (0:ℤ) ≤ 1)] at h1
        have h2 := ih (by omega)
        rw [abs_le] at h2 ⊢
        push_cast
        omega
    refine ⟨fun i : Fin (N + 1) => s i, ?_, ?_⟩
    · rw [Set.mem_pi]
      intro i _
      have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.isLt
      have := bd i hi
      rw [abs_le] at this
      show -(N:ℤ) ≤ s i ∧ s i ≤ N
      constructor <;> omega
    · funext j
      by_cases h : j < N + 1
      · simp [h]
      · have : s j = 0 := hz j (by omega)
        simp [h, this]
  have witness : ∀ n, 1 ≤ n → ∃ s : ℕ → ℤ, s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧
      (∀ j ∈ Set.Icc 1 (2 * n), |s j - s (j - 1)| = 1) := by
    intro n hn
    refine ⟨fun j => if j ≤ n then (j:ℤ) else if j ≤ 2 * n then 2 * (n:ℤ) - (j:ℤ) else 0,
      ?_, ?_, ?_⟩
    · simp
    · intro j hj
      dsimp only
      split_ifs <;> omega
    · intro j hj
      obtain ⟨hj1, hjN⟩ := Set.mem_Icc.mp hj
      dsimp only
      split_ifs <;> rw [abs_eq (by norm_num : (0:ℤ) ≤ 1)] <;> omega
  have main : ∀ n, 1 ≤ n → ∀ g : (ℕ → ℤ) → ℝ,
      (∀ s, g s = 1 / (1 + ∑ j ∈ Finset.Icc 1 (2 * n - 1), (3:ℝ) ^ (s j))) →
      (∑' v : {s : ℕ → ℤ | s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧
          (∀ j ∈ Set.Icc 1 (2 * n), |s j - s (j - 1)| = 1)}, g v.1)
        / ((({s : ℕ → ℤ | s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧
          (∀ j ∈ Set.Icc 1 (2 * n), |s j - s (j - 1)| = 1)} : Set (ℕ → ℤ)).ncard : ℝ))
        = 1 / ((2 * n : ℕ) : ℝ) := by
    intro n hn g hg
    obtain ⟨F, hF⟩ : ∃ F : Finset (ℕ → ℤ), ∀ s, s ∈ F ↔ (s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧
        (∀ j ∈ Set.Icc 1 (2 * n), |s j - s (j - 1)| = 1)) :=
      ⟨(finP (2 * n)).toFinset, fun s => (finP (2 * n)).mem_toFinset⟩
    have hPF : {s : ℕ → ℤ | s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧
        (∀ j ∈ Set.Icc 1 (2 * n), |s j - s (j - 1)| = 1)} = ↑F := by
      ext s; simp only [Set.mem_ofPred_eq, Finset.mem_coe, hF]
    have hT : ∑' v : {s : ℕ → ℤ | s 0 = 0 ∧ (∀ j ≥ 2 * n, s j = 0) ∧
        (∀ j ∈ Set.Icc 1 (2 * n), |s j - s (j - 1)| = 1)}, g v.1 = ∑ v ∈ F, g v := by
      rw [hPF]; exact Finset.tsum_subtype F g
    rw [hT, hPF, Set.ncard_coe_finset]
    have hne : F.card ≠ 0 := by
      obtain ⟨w, hw⟩ := witness n hn
      exact (Finset.card_pos.mpr ⟨w, (hF w).mpr hw⟩).ne'
    have hN : 0 < 2 * n := by omega
    have C1 : ∀ k ∈ Finset.range (2 * n),
        ∑ v ∈ F, g (rot (2 * n) k v) = ∑ v ∈ F, g v := by
      intro k hk
      apply Finset.sum_nbij' (rot (2 * n) k) (rot (2 * n) (2 * n - k))
      · intro a ha
        obtain ⟨h0, hz, hs⟩ := (hF a).mp ha
        exact (hF _).mpr (rot_mem (2 * n) k a hN h0 hz hs)
      · intro a ha
        obtain ⟨h0, hz, hs⟩ := (hF a).mp ha
        exact (hF _).mpr (rot_mem (2 * n) (2 * n - k) a hN h0 hz hs)
      · intro a ha
        obtain ⟨h0, hz, hs⟩ := (hF a).mp ha
        have hk' : k < 2 * n := Finset.mem_range.mp hk
        exact rot_rot (2 * n) k (2 * n - k) a h0 hz
          (by rw [show k + (2 * n - k) = 2 * n by omega, Nat.mod_self]) hN
      · intro a ha
        obtain ⟨h0, hz, hs⟩ := (hF a).mp ha
        have hk' : k < 2 * n := Finset.mem_range.mp hk
        exact rot_rot (2 * n) (2 * n - k) k a h0 hz
          (by rw [show 2 * n - k + k = 2 * n by omega, Nat.mod_self]) hN
      · intro a _; rfl
    have C2 : ((2 * n : ℕ) : ℝ) * ∑ v ∈ F, g v = (F.card : ℝ) := by
      have e1 : ∑ k ∈ Finset.range (2 * n), ∑ v ∈ F, g (rot (2 * n) k v)
          = ((2 * n : ℕ) : ℝ) * ∑ v ∈ F, g v := by
        rw [Finset.sum_congr rfl C1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have e2 : ∑ k ∈ Finset.range (2 * n), ∑ v ∈ F, g (rot (2 * n) k v) = (F.card : ℝ) := by
        rw [Finset.sum_comm]
        have hv : ∀ v ∈ F, ∑ k ∈ Finset.range (2 * n), g (rot (2 * n) k v) = 1 := by
          intro v _
          simp only [hg]
          exact Bl (2 * n) v hN
        rw [Finset.sum_congr rfl hv]
        simp
      linarith [e1, e2]
    rw [div_eq_div_iff (by exact_mod_cast hne) (by exact_mod_cast hN.ne')]
    linarith [C2]
  subst hV hq hM
  have := main 2020 (by norm_num) (fun s => 1 / (1 + ∑ j ∈ Finset.Icc 1 (2 * 2020 - 1),
    (3:ℝ) ^ (s j))) (fun s => rfl)
  simpa [putnam_2020_b4_solution] using this
