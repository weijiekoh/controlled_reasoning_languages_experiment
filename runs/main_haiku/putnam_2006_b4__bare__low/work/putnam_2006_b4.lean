import Mathlib

noncomputable abbrev putnam_2006_b4_solution : ℕ → ℕ := fun k ↦ 2 ^ k
/--
Let $Z$ denote the set of points in $\mathbb{R}^n$ whose coordinates are $0$ or $1$. (Thus $Z$ has $2^n$ elements, which are the vertices of a unit hypercube in $\mathbb{R}^n$.) Given a vector subspace $V$ of $\mathbb{R}^n$, let $Z(V)$ denote the number of members of $Z$ that lie in $V$. Let $k$ be given, $0 \leq k \leq n$. Find the maximum, over all vector subspaces $V \subseteq \mathbb{R}^n$ of dimension $k$, of the number of points in $V \cap Z$.
-/
theorem putnam_2006_b4
    (n k : ℕ)
    (npos : n > 0)
    (hk : k ≤ n)
    (Z : Set (Fin n → ℝ))
    (hZ : Z = {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1}) :
    IsGreatest
      {y | ∃ V : Subspace ℝ (Fin n → ℝ), Module.rank ℝ V = k ∧ (Z ∩ V).ncard = y}
      (putnam_2006_b4_solution k) := by
  have pb4_aux : ∀ (m : ℕ) (W : Subspace ℝ (Fin n → ℝ)), Module.finrank ℝ W ≤ m →
      ∃ T : Finset (Fin n), T.card ≤ m ∧ ∀ v ∈ W, (∀ j ∈ T, v j = 0) → v = 0 := by
    intro m
    induction m with
    | zero =>
      intro W hW
      refine ⟨∅, by simp, ?_⟩
      intro v hv _
      have h0 : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
      rw [h0] at hv
      exact (Submodule.mem_bot ℝ).mp hv
    | succ m ih =>
      intro W hW
      by_cases hbot : W = ⊥
      · refine ⟨∅, by simp, ?_⟩
        intro v hv _
        rw [hbot] at hv
        exact (Submodule.mem_bot ℝ).mp hv
      · obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot
        obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
          by_contra h
          push Not at h
          exact hv0 (funext h)
        obtain ⟨W', hW'⟩ : ∃ W' : Subspace ℝ (Fin n → ℝ),
            W' = W ⊓ LinearMap.ker (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) := ⟨_, rfl⟩
        have hlt : W' < W := by
          refine lt_of_le_of_ne (by rw [hW']; exact inf_le_left) ?_
          intro h
          have hvW' : v ∈ W' := by rw [h]; exact hvW
          rw [hW'] at hvW'
          have := (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hvW').2)
          simp at this
          exact hj this
        have hfin : Module.finrank ℝ W' < Module.finrank ℝ W :=
          Submodule.finrank_lt_finrank_of_lt hlt
        obtain ⟨T', hT'card, hT'⟩ := ih W' (by omega)
        refine ⟨insert j T', ?_, ?_⟩
        · have := Finset.card_insert_le j T'
          omega
        · intro u huW hu
          have huj : u j = 0 := hu j (Finset.mem_insert_self _ _)
          have huW' : u ∈ W' := by
            rw [hW']
            exact Submodule.mem_inf.mpr ⟨huW, LinearMap.mem_ker.mpr (by simpa using huj)⟩
          exact hT' u huW' (fun i hi => hu i (Finset.mem_insert_of_mem hi))
  subst hZ
  have hZfin : {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ⊆
      Set.range (fun f : Fin n → Bool => fun j => if f j then (1:ℝ) else 0) := by
    intro P hP
    refine ⟨fun j => decide (P j = 1), ?_⟩
    funext j
    rcases hP j with h | h <;> simp [h]
  have upper : ∀ V : Subspace ℝ (Fin n → ℝ), Module.rank ℝ V = k →
      ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ V).ncard ≤ 2 ^ k := by
    intro V hV
    have hf : Module.finrank ℝ V = k := by
      have h : ((Module.finrank ℝ V : ℕ) : Cardinal) = (k : Cardinal) := by
        rw [Module.finrank_eq_rank, hV]
      exact_mod_cast h
    obtain ⟨T, hTc, hT⟩ := pb4_aux k V hf.le
    have hle : ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ V).ncard ≤
        (Set.univ : Set (T → Bool)).ncard := by
      apply Set.ncard_le_ncard_of_injOn (fun P : Fin n → ℝ => fun j : T => decide (P j.1 = 1))
      · intro P _
        exact Set.mem_univ _
      · rintro P ⟨hP, hPV⟩ Q ⟨hQ, hQV⟩ hPQ
        have hTeq : ∀ j ∈ T, P j = Q j := by
          intro j hj
          have := congrFun hPQ ⟨j, hj⟩
          simp only [decide_eq_decide] at this
          rcases hP j with h1 | h1 <;> rcases hQ j with h2 | h2 <;>
            simp_all
        have hz := hT (P - Q) (V.sub_mem hPV hQV) (fun j hj => by
          simp [hTeq j hj])
        exact sub_eq_zero.mp hz
    have hcard : (Set.univ : Set (T → Bool)).ncard = 2 ^ T.card := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card]
      simp [Fintype.card_bool]
    rw [hcard] at hle
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) hTc)
  -- the coordinate subspace
  let L : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun f j => if h : j.val < k then f ⟨j.val, h⟩ else 0
      map_add' := by
        intro a b; funext j
        by_cases h : j.val < k <;> simp [h]
      map_smul' := by
        intro c a; funext j
        by_cases h : j.val < k <;> simp [h] }
  have hL : ∀ f : Fin k → ℝ, ∀ i : Fin k, L f (Fin.castLE hk i) = f i := by
    intro f i
    simp [L]
  have hinj : Function.Injective L := by
    intro a b hab
    funext i
    have := congrArg (fun P : Fin n → ℝ => P (Fin.castLE hk i)) hab
    simp only [hL] at this
    exact this
  have hrank : Module.rank ℝ (LinearMap.range L) = (k : Cardinal) := by
    rw [rank_range_of_injective L hinj]
    simp
  constructor
  · show ∃ V : Subspace ℝ (Fin n → ℝ), Module.rank ℝ V = k ∧
      ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ V).ncard = 2 ^ k
    refine ⟨LinearMap.range L, hrank, ?_⟩
    apply le_antisymm (upper _ hrank)
    let g : (Fin k → Bool) → (Fin n → ℝ) := fun f => L (fun i => if f i then 1 else 0)
    have hgi : Function.Injective g := by
      intro f f' h
      funext i
      have := congrArg (fun P : Fin n → ℝ => P (Fin.castLE hk i)) h
      simp only [g, hL] at this
      cases hfi : f i <;> cases hfi' : f' i <;> simp_all
    have hsub : g '' Set.univ ⊆
        {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ LinearMap.range L := by
      rintro P ⟨f, _, rfl⟩
      refine ⟨?_, ⟨_, rfl⟩⟩
      intro j
      by_cases h : j.val < k
      · simp only [g, L, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
        split <;> simp
      · simp only [g, L, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]
        simp
    have hfin : ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩
        LinearMap.range L).Finite :=
      (Set.finite_range _).subset (fun P hP => hZfin hP.1)
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_image_of_injective _ hgi, Set.ncard_univ, Nat.card_eq_fintype_card] at h1
    simpa [Fintype.card_bool] using h1
  · rintro y ⟨V, hV, rfl⟩
    exact upper V hV
