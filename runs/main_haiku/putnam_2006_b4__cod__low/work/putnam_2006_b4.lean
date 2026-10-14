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
      {y | ∃ V : Subspace ℝ (Fin n → ℝ), Module.rank ℝ V = k ∧ (Z ∩ (V : Set (Fin n → ℝ))).ncard = y}
      (putnam_2006_b4_solution k) := by
  classical
  subst hZ
  -- Upper bound for any k-dimensional subspace
  have hZfin : Set.Finite {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} := by
    apply (Set.finite_range (fun c : Fin n → Bool => fun j => if c j then (1:ℝ) else 0)).subset
    intro P hP
    refine ⟨fun j => decide (P j = 1), ?_⟩
    funext j
    rcases hP j with h | h <;> simp [h]
  have upper : ∀ V : Subspace ℝ (Fin n → ℝ), Module.finrank ℝ V = k →
      ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (V : Set (Fin n → ℝ))).ncard ≤ 2 ^ k := by
    intro V hV
    let φ : Fin n → Module.Dual ℝ V := fun i => (LinearMap.proj i).comp V.subtype
    have hφ : ∀ i (v : V), φ i v = v.1 i := fun i v => rfl
    obtain ⟨B, hBR, hBspan, hBli⟩ := exists_linearIndependent ℝ (Set.range φ)
    have hspan : Submodule.span ℝ (Set.range φ) = ⊤ := by
      by_contra hne
      obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
        (lt_of_le_of_ne le_top hne) inferInstance
      set v := (Module.evalEquiv ℝ V).symm f with hvdef
      have hfv : ∀ g : Module.Dual ℝ V, f g = g v := by
        intro g
        have : f = Module.evalEquiv ℝ V v := by simp [hvdef]
        rw [this]; rfl
      have hzero : ∀ i, φ i v = 0 := by
        intro i
        have hmem : φ i ∈ Submodule.span ℝ (Set.range φ) := Submodule.subset_span (Set.mem_range_self i)
        have h := Submodule.mem_map_of_mem (f := f) hmem
        rw [hfW] at h
        have h2 : f (φ i) = 0 := by simpa using h
        rw [hfv] at h2; exact h2
      have hv : v = 0 := by
        apply Subtype.ext
        funext i
        rw [← hφ]; simp [hzero i]
      apply hf0
      have : f = Module.evalEquiv ℝ V v := by simp [hvdef]
      rw [this, hv]; simp
    have hBfin : Finite B := hBli.finite
    have := Fintype.ofFinite B
    have hBcard : Fintype.card B ≤ k := by
      have := hBli.fintype_card_le_finrank
      rw [Subspace.dual_finrank_eq, hV] at this
      exact this
    obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → (B → ℝ), ∀ P (hP : P ∈ V) (b : B),
        f P b = (b.1) ⟨P, hP⟩ := by
      refine ⟨fun P => fun b => if hP : P ∈ V then (b.1) ⟨P, hP⟩ else 0, ?_⟩
      intro P hP b
      simp [hP]
    have hinj : Function.Injective (fun c : B → Bool => fun b => if c b then (1:ℝ) else 0) := by
      intro c d h
      funext b
      have := congrFun h b
      by_cases hc : c b <;> by_cases hd : d b <;> simp_all
    have hT : ((fun c : B → Bool => fun b => if c b then (1:ℝ) else 0) '' Set.univ).ncard ≤ 2 ^ k := by
      rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_fun, Fintype.card_bool]
      exact Nat.pow_le_pow_right (by norm_num) hBcard
    have hmaps : ∀ P ∈ {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (V : Set (Fin n → ℝ)),
        f P ∈ (fun c : B → Bool => fun b => if c b then (1:ℝ) else 0) '' Set.univ := by
      rintro P ⟨hPZ, hPV⟩
      have hval : ∀ b : B, f P b = 0 ∨ f P b = 1 := by
        intro b
        obtain ⟨i, hi⟩ := hBR b.2
        rw [hf P hPV b, ← hi, hφ]
        exact hPZ i
      refine ⟨fun b => decide (f P b = 1), Set.mem_univ _, ?_⟩
      funext b
      rcases hval b with h | h <;> simp [h]
    have hinjOn : Set.InjOn f ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (V : Set (Fin n → ℝ))) := by
      rintro P ⟨-, hP⟩ Q ⟨-, hQ⟩ hPQ
      have key : ∀ b : B, (b.1) ⟨P, hP⟩ = (b.1) ⟨Q, hQ⟩ := by
        intro b
        have := congrFun hPQ b
        rwa [hf P hP b, hf Q hQ b] at this
      have hle : Submodule.span ℝ B ≤
          LinearMap.ker (Module.Dual.eval ℝ V (⟨P, hP⟩ - ⟨Q, hQ⟩)) := by
        rw [Submodule.span_le]
        intro b hb
        have := key ⟨b, hb⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, map_sub]
        exact sub_eq_zero.mpr this
      have hall : ∀ g : Module.Dual ℝ V, g (⟨P, hP⟩ - ⟨Q, hQ⟩) = 0 := by
        intro g
        have hg : g ∈ Submodule.span ℝ B := by
          rw [hBspan, hspan]; exact Submodule.mem_top
        have := hle hg
        simpa using this
      have hd : (⟨P, hP⟩ - ⟨Q, hQ⟩ : V) = 0 := by
        rw [← Module.forall_dual_apply_eq_zero_iff ℝ]
        exact hall
      have := congrArg Subtype.val (sub_eq_zero.mp hd)
      exact this
    calc ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩ (V : Set (Fin n → ℝ))).ncard
        ≤ ((fun c : B → Bool => fun b => if c b then (1:ℝ) else 0) '' Set.univ).ncard :=
          Set.ncard_le_ncard_of_injOn f hmaps hinjOn (Set.finite_univ.image _)
      _ ≤ 2 ^ k := hT
  -- the example subspace
  let e : Fin k → Fin n → ℝ := fun i => Pi.single (Fin.castLE hk i) 1
  have hli : LinearIndependent ℝ e := by
    have := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp (Fin.castLE hk)
      (Fin.castLE_injective hk)
    convert this using 1
    funext i
    simp [e]
  have hVfin : Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = k := by
    have := finrank_span_eq_card hli
    simpa using this
  have hev : ∀ (c : Fin k → ℝ) (j : Fin n),
      (∑ i, c i • e i) j = if h : j.val < k then c ⟨j.val, h⟩ else 0 := by
    intro c j
    simp only [Finset.sum_apply, Pi.smul_apply, e, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    split_ifs with h1
    · rw [Finset.sum_eq_single ⟨j.val, h1⟩]
      · simp [Fin.ext_iff]
      · intro b _ hb
        have : ¬ (Fin.castLE hk b = j) := by
          intro hc; apply hb; ext; simp [← hc]
        simp only [if_neg this, if_neg (fun hc : j = Fin.castLE hk b => this hc.symm)]
      · simp [Fin.ext_iff]
    · apply Finset.sum_eq_zero
      intro i _
      have : ¬ (Fin.castLE hk i = j) := by
        intro hc; apply h1; rw [← hc]; simp
      simp only [if_neg this, if_neg (fun hc : j = Fin.castLE hk i => this hc.symm)]
  let h : (Fin k → Bool) → (Fin n → ℝ) := fun b => ∑ i, (if b i then (1:ℝ) else 0) • e i
  have hhV : ∀ b, h b ∈ Submodule.span ℝ (Set.range e) := fun b =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  have hhZ : ∀ b, ∀ j : Fin n, h b j = 0 ∨ h b j = 1 := by
    intro b j
    simp only [h, hev]
    split_ifs with h1
    all_goals first
      | (cases hb : b ⟨j.val, h1⟩ <;> simp [hb])
      | simp
  have hinjh : Function.Injective h := by
    intro b c hbc
    funext i
    have := congrFun hbc (Fin.castLE hk i)
    simp only [h, hev] at this
    simp only [Fin.val_castLE, Fin.is_lt, dif_pos, Fin.eta] at this
    by_cases hb : b i <;> by_cases hc : c i <;> simp_all
  have hsub : h '' Set.univ ⊆ {P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩
      Submodule.span ℝ (Set.range e) := by
    rintro _ ⟨b, -, rfl⟩
    exact ⟨hhZ b, hhV b⟩
  have hlow : 2 ^ k ≤ ({P : Fin n → ℝ | ∀ j : Fin n, P j = 0 ∨ P j = 1} ∩
      Submodule.span ℝ (Set.range e)).ncard := by
    have h1 := Set.ncard_le_ncard hsub (hZfin.subset Set.inter_subset_left)
    rw [Set.ncard_image_of_injective _ hinjh, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
    exact h1
  have hup := upper _ hVfin
  have hrank : Module.rank ℝ (Submodule.span ℝ (Set.range e)) = (k : Cardinal) := by
    rw [← Module.finrank_eq_rank, hVfin]
  refine ⟨⟨Submodule.span ℝ (Set.range e), hrank, le_antisymm hup hlow⟩, ?_⟩
  rintro y ⟨V, hVr, rfl⟩
  apply upper V
  have : (Module.finrank ℝ V : Cardinal) = (k : Cardinal) := by
    rw [Module.finrank_eq_rank, hVr]
  exact_mod_cast this
