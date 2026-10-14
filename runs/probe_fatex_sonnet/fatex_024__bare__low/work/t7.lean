import Mathlib

lemma nsq {I : Type} (p : I → ℕ) (hp : ∀ i, (p i).Prime) (h_inj : p.Injective)
    (T : Finset I) (hT : T.Nonempty) : ¬ IsSquare (∏ i ∈ T, p i) := by
  classical
  rintro ⟨k, hk⟩
  obtain ⟨i, hi⟩ := hT
  have h1 : p i ∣ k * k := by
    rw [← hk]; exact Finset.dvd_prod_of_mem _ hi
  have h2 : p i ∣ k := by
    rcases (Nat.Prime.dvd_mul (hp i)).1 h1 with h | h <;> exact h
  obtain ⟨m, hm⟩ := h2
  have h3 : ∏ l ∈ T, p l = p i * ∏ l ∈ T.erase i, p l := (Finset.mul_prod_erase T p hi).symm
  have h4 : p i * ∏ l ∈ T.erase i, p l = p i * (p i * m * m) := by
    rw [← h3, hk, hm]; ring
  have h5 : ∏ l ∈ T.erase i, p l = p i * m * m := Nat.eq_of_mul_eq_mul_left (hp i).pos h4
  have h6 : p i ∣ ∏ l ∈ T.erase i, p l := by rw [h5]; exact ⟨m * m, by ring⟩
  rw [Prime.dvd_finsetProd_iff (hp i).prime] at h6
  obtain ⟨l, hl, hdl⟩ := h6
  rw [Nat.prime_dvd_prime_iff_eq (hp i) (hp l)] at hdl
  have := h_inj hdl
  have := (Finset.mem_erase.1 hl).1
  simp_all

abbrev RS {I : Type} (p : I → ℕ) : Type :=
  Algebra.adjoin ℚ (Set.range (fun i ↦ Real.sqrt (p i)))

lemma fixedLemma {I : Type} [Finite I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (x : RS p) (hx : ∀ σ : RS p ≃ₐ[ℚ] RS p, σ x = x) : ∃ q : ℚ, (x : ℝ) = q := by
  sorry

theorem main {I : Type} [Finite I] (p : I → ℕ)
    (hp : ∀ (i : I), (p i).Prime) (h_inj : p.Injective) :
    Nonempty ((RS p ≃ₐ[ℚ] RS p) ≃* (Multiplicative (I → (ZMod 2)))) := by
  classical
  haveI := Fintype.ofFinite I
  let x : I → RS p := fun i => ⟨Real.sqrt (p i), Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hxsq : ∀ i, x i ^ 2 = algebraMap ℚ (RS p) (p i : ℚ) := by
    intro i
    apply Subtype.ext
    simp [x, Real.sq_sqrt]
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i h
    have := congrArg (fun y : RS p => (y : ℝ)) h
    simp [x] at this
    exact (hp i).ne_zero this
  have hsign : ∀ (σ : RS p ≃ₐ[ℚ] RS p) i, σ (x i) = x i ∨ σ (x i) = - x i := by
    intro σ i
    have : (σ (x i))^2 = (x i)^2 := by
      rw [← map_pow, hxsq, AlgEquiv.commutes]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  have hneg : ∀ i, - x i ≠ x i := by
    intro i h
    have : x i = 0 := by
      have : (2:RS p) * x i = 0 := by linear_combination -h
      rcases mul_eq_zero.1 this with h | h
      · exfalso
        have := congrArg (fun y : RS p => (y : ℝ)) h
        simp at this
      · exact h
    exact hx0 i this
  let φ : (RS p ≃ₐ[ℚ] RS p) → I → ZMod 2 := fun σ i => if σ (x i) = x i then 0 else 1
  have hφ1 : ∀ i, φ 1 i = 0 := by intro i; simp [φ]
  have hφmul : ∀ σ τ i, φ (σ * τ) i = φ σ i + φ τ i := by
    intro σ τ i
    simp only [φ, AlgEquiv.mul_apply]
    rcases hsign τ i with h | h
    · simp [h]
    · rcases hsign σ i with h' | h'
      · simp [h, h', hneg i]
      · simp [h, h', hneg i]; decide
  let Φ : (RS p ≃ₐ[ℚ] RS p) →* Multiplicative (I → ZMod 2) :=
    { toFun := fun σ => Multiplicative.ofAdd (φ σ)
      map_one' := by ext i; exact hφ1 i
      map_mul' := by intro σ τ; ext i; exact hφmul σ τ i }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h0 : ∀ i, φ σ i = 0 := fun i => congrFun hσ i
    have hfix : ∀ i, σ (x i) = x i := by
      intro i
      have := h0 i
      simp only [φ] at this
      by_contra hc
      simp [hc] at this
    refine AlgEquiv.ext ?_
    rintro ⟨y, hy⟩
    rw [AlgEquiv.one_apply]
    refine Algebra.adjoin_induction (p := fun y hy => σ ⟨y, hy⟩ = ⟨y, hy⟩) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, rfl⟩; exact hfix i
    · intro r; exact σ.commutes r
    · intro a b ha hb h1 h2
      exact (map_add σ ⟨a, ha⟩ ⟨b, hb⟩).trans (by rw [h1, h2])
    · intro a b ha hb h1 h2
      exact (map_mul σ ⟨a, ha⟩ ⟨b, hb⟩).trans (by rw [h1, h2])
  have hsurj : Function.Surjective Φ := by
    let H : Submodule (ZMod 2) (I → ZMod 2) :=
      { carrier := {v | ∃ σ, φ σ = v}
        add_mem' := by
          rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
          exact ⟨σ * τ, funext fun i => hφmul σ τ i⟩
        zero_mem' := ⟨1, funext hφ1⟩
        smul_mem' := by
          intro c v hv
          have hc : c = 0 ∨ c = 1 := by revert c; decide
          rcases hc with rfl | rfl
          · rw [zero_smul]; exact ⟨1, funext hφ1⟩
          · rw [one_smul]; exact hv }
    have hH : H = ⊤ := by
      by_contra hne
      obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top H (lt_top_iff_ne_top.2 hne)
      let c : I → ZMod 2 := fun i => f (fun j => if i = j then 1 else 0)
      have hfv : ∀ v, f v = ∑ i, v i * c i := by
        intro v
        rw [LinearMap.pi_apply_eq_sum_univ f v]
        simp [c]
      let T : Finset I := Finset.univ.filter (fun i => c i ≠ 0)
      have hc1 : ∀ i ∈ T, c i = 1 := by
        intro i hi
        have : c i ≠ 0 := (Finset.mem_filter.1 hi).2
        generalize c i = a at this
        revert a; decide
      have hTne : T.Nonempty := by
        by_contra hT
        rw [Finset.not_nonempty_iff_eq_empty] at hT
        apply hf0
        refine LinearMap.ext fun v => ?_
        rw [hfv, LinearMap.zero_apply]
        apply Finset.sum_eq_zero
        intro i _
        by_contra hne
        have : i ∈ T := by simp only [T, Finset.mem_filter]; exact ⟨Finset.mem_univ _, right_ne_zero_of_mul hne⟩
        rw [hT] at this; simp at this
      let y : RS p := ∏ i ∈ T, x i
      have hσy : ∀ σ : RS p ≃ₐ[ℚ] RS p, σ y = y := by
        intro σ
        have hs : ∀ i, σ (x i) = (-1 : RS p) ^ (φ σ i).val * x i := by
          intro i
          rcases hsign σ i with h | h
          · have : φ σ i = 0 := by simp [φ, h]
            rw [h, this]; simp
          · have : φ σ i = 1 := by simp [φ, h, hneg i]
            have hv1 : (1 : ZMod 2).val = 1 := rfl
            rw [h, this, hv1]; simp
        have hev : 2 ∣ ∑ i ∈ T, (φ σ i).val := by
          rw [← ZMod.natCast_eq_zero_iff]
          have h1 : f (φ σ) = 0 := hle ⟨σ, rfl⟩
          rw [hfv] at h1
          push_cast
          simp only [ZMod.natCast_zmod_val]
          rw [← h1]
          calc ∑ i ∈ T, φ σ i = ∑ i ∈ T, φ σ i * c i := by
                apply Finset.sum_congr rfl; intro i hi; rw [hc1 i hi, mul_one]
            _ = ∑ i, φ σ i * c i := by
                apply Finset.sum_subset (Finset.subset_univ _)
                intro i _ hi
                have : c i = 0 := by by_contra h; exact hi (by simp [T, h])
                rw [this, mul_zero]
        calc σ y = ∏ i ∈ T, σ (x i) := map_prod σ _ _
          _ = ∏ i ∈ T, ((-1 : RS p) ^ (φ σ i).val * x i) := Finset.prod_congr rfl fun i _ => hs i
          _ = (-1 : RS p) ^ (∑ i ∈ T, (φ σ i).val) * y := by
                rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
          _ = y := by
                obtain ⟨k, hk⟩ := hev
                rw [hk, pow_mul]; simp
      obtain ⟨q, hq⟩ := fixedLemma p hp y hσy
      have hyR : (y : ℝ) = ∏ i ∈ T, Real.sqrt (p i) := by
        simp [y, x]
      have hN : ((∏ i ∈ T, p i : ℕ) : ℝ) = q ^ 2 := by
        rw [Nat.cast_prod, ← hq, hyR, ← Finset.prod_pow]
        exact Finset.prod_congr rfl (fun i _ => (Real.sq_sqrt (by positivity)).symm)
      have hirr : Irrational (Real.sqrt ((∏ i ∈ T, p i : ℕ) : ℝ)) :=
        irrational_sqrt_natCast_iff.2 (nsq p hp h_inj T hTne)
      apply hirr
      refine ⟨|q|, ?_⟩
      rw [hN, Real.sqrt_sq_eq_abs]; simp
    intro v
    have hv : Multiplicative.toAdd v ∈ H := by rw [hH]; trivial
    obtain ⟨σ, hσ⟩ := hv
    exact ⟨σ, by show Multiplicative.ofAdd (φ σ) = v; rw [hσ]; rfl⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩
