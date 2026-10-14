import Mathlib

open Polynomial IntermediateField

/--
Let $f(X)=X^4-X^2-1\in \mathbb{Q}[X]$, $K$ is the splitting field of $f$ over $\mathbb{Q}$,
prove that the number of intermediate fields of $K/\mathbb{Q}$ is 10.
-/
theorem card_intermediateField_splittingField_eq_ten :
    Nat.card (IntermediateField ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField) = 10 := by
  -- group theory part
  have card_sub : ∀ (M : Type) [Group M] [Fintype M] [DecidableEq M],
      Nat.card (Subgroup M) = Fintype.card {s : Finset M // 1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ ∀ a ∈ s, a⁻¹ ∈ s} := by
    intro M _ _ _
    classical
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact
    { toFun := fun H => ⟨Finset.univ.filter (· ∈ H), by simp; intros; exact H.mul_mem ‹_› ‹_›⟩
      invFun := fun s => { carrier := {x | x ∈ s.1}, mul_mem' := fun ha hb => s.2.2.1 _ ha _ hb, one_mem' := s.2.1, inv_mem' := fun ha => s.2.2.2 _ ha }
      left_inv := fun H => by ext x; simp
      right_inv := fun s => by ext x; simp }
  have d4 : Nat.card (Subgroup (DihedralGroup 4)) = 10 := by
    rw [card_sub]; decide
  have hψ : ∃ ψ : DihedralGroup 4 →* Equiv.Perm (Fin 4), Function.Injective ψ ∧
      (∀ σ : Equiv.Perm (Fin 4), σ * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * σ → ∃ x, ψ x = σ) := by
    refine ⟨MonoidHom.mk' (fun x : DihedralGroup 4 => match x with
      | .r i => (Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ^ i.val
      | .sr i => Equiv.swap 0 1 * (Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ^ i.val) (by decide), by decide, by decide⟩
  have card_sub_equiv : ∀ {G H : Type} [Group G] [Group H] (e : G ≃* H),
      Nat.card (Subgroup G) = Nat.card (Subgroup H) := by
    intro G H _ _ e
    apply Nat.card_congr
    exact
    { toFun := Subgroup.map e.toMonoidHom
      invFun := Subgroup.map e.symm.toMonoidHom
      left_inv := fun K => by
        ext x; simp [Subgroup.mem_map]
      right_inv := fun K => by
        ext x; simp [Subgroup.mem_map] }
  have grp_main : ∀ (G : Type) [Group G] [Finite G] (f : G →* Equiv.Perm (Fin 4)), Function.Injective f →
      (∀ g, f g * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * f g) →
      8 ≤ Nat.card G → Nat.card (Subgroup G) = 10 := by
    intro G _ _ f hf hc hG
    obtain ⟨ψ, ψinj, ψrange⟩ := hψ
    have hmem : ∀ g, f g ∈ ψ.range := fun g => by
      obtain ⟨x, hx⟩ := ψrange (f g) (hc g)
      exact ⟨x, hx⟩
    let k : G →* DihedralGroup 4 :=
      ((MonoidHom.ofInjective ψinj).symm : ψ.range →* DihedralGroup 4).comp
        (f.codRestrict ψ.range hmem)
    have kinj : Function.Injective k := by
      intro a b h
      apply hf
      have := (MonoidHom.ofInjective ψinj).symm.injective h
      simpa using congrArg Subtype.val this
    have hD : Nat.card (DihedralGroup 4) = 8 := by
      rw [Nat.card_eq_fintype_card]; decide
    have hle : Nat.card G ≤ 8 := by
      rw [← hD]; exact Nat.card_le_card_of_injective k kinj
    have kb : Function.Bijective k := by
      rw [Nat.bijective_iff_injective_and_card]
      exact ⟨kinj, by rw [hD]; omega⟩
    rw [card_sub_equiv (MulEquiv.ofBijective k kb), d4]
  -- irreducibility
  have sq5 : ∀ y : ℚ, y ^ 2 ≠ 5 := by
    intro y h
    have h5 : IsSquare ((5:ℕ):ℚ) := ⟨y, by push_cast; nlinarith⟩
    have := Rat.isSquare_natCast_iff.mp h5
    obtain ⟨m, hm⟩ := this
    have : m ≤ 3 := by nlinarith
    interval_cases m <;> omega
  have no_rat_root : ∀ x : ℚ, x ^ 4 - x ^ 2 - 1 ≠ 0 := by
    intro x h
    exact sq5 (2 * x ^ 2 - 1) (by nlinarith)
  have quad_form : ∀ (p : ℚ[X]), p.Monic → p.natDegree = 2 →
      p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    intro p hp h
    rcases n with _ | _ | _ | n
    · simp
    · simp
    · have := hp.coeff_natDegree
      rw [h] at this; simp [coeff_X_pow, coeff_X, this]
    · have : p.coeff (n+3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [this]; simp [coeff_X, coeff_X_pow]
  
  have lin_form : ∀ (p : ℚ[X]), p.Monic → p.natDegree = 1 → p = X + C (p.coeff 0) := by
    intro p hp h
    rcases n with _ | _ | n
    · simp
    · have := hp.coeff_natDegree
      rw [h] at this; simpa using this
    · have : p.coeff (n+2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [this]; simp [coeff_X, coeff_C]
  
  have f_irred : Irreducible (X ^ 4 - X ^ 2 - 1 : ℚ[X]) := by
    have hm : (X ^ 4 - X ^ 2 - 1 : ℚ[X]).Monic := by monicity!
    have hdeg : (X ^ 4 - X ^ 2 - 1 : ℚ[X]).natDegree = 4 := by compute_degree!
    rw [hm.irreducible_iff_natDegree]
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg natDegree h
      rw [hdeg, natDegree_one] at this
      omega
    intro p q hp hq hpq
    have hd : p.natDegree + q.natDegree = 4 := by
      rw [← natDegree_mul hp.ne_zero hq.ne_zero, hpq, hdeg]
    have lin : ∀ p q : ℚ[X], p.Monic → p.natDegree = 1 → p * q = X ^ 4 - X ^ 2 - 1 → False := by
      intro p q hp h1 h
      have hp' := lin_form p hp h1
      have := congrArg (eval (-(p.coeff 0))) h
      rw [eval_mul] at this
      have h0 : eval (-(p.coeff 0)) p = 0 := by
        conv_lhs => rw [hp']
        simp
      rw [h0] at this
      simp at this
      exact no_rat_root _ (by linarith)
    by_contra hcon
    push_neg at hcon
    have : p.natDegree = 1 ∨ p.natDegree = 2 ∨ p.natDegree = 3 := by omega
    rcases this with h1 | h2 | h3
    · exact lin p q hp h1 hpq
    · have hq2 : q.natDegree = 2 := by omega
      have e1 := quad_form p hp h2
      have e2 := quad_form q hq hq2
      set a := p.coeff 1
      set b := p.coeff 0
      set c := q.coeff 1
      set d := q.coeff 0
      rw [e1, e2] at hpq
      have key : (X ^ 2 + C a * X + C b) * (X ^ 2 + C c * X + C d) = X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X + C (b * d) := by
        simp only [C_add, C_mul]; ring
      rw [key] at hpq
      have c0 := congrArg (coeff · 0) hpq
      have c1 := congrArg (coeff · 1) hpq
      have c2 := congrArg (coeff · 2) hpq
      have c3 := congrArg (coeff · 3) hpq
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at c0 c1 c2 c3
      norm_num at c0 c1 c2 c3
      have hc : c = -a := by linarith
      rw [hc] at c1 c2
      have h3 : a * (d - b) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h | h
      · rw [h] at c2
        have hd : d = -1 - b := by linarith
        rw [hd] at c0
        exact sq5 (2 * b + 1) (by nlinarith)
      · have : d = b := by linarith
        rw [this] at c0
        nlinarith [sq_nonneg b]
    · exact lin q p hq (by omega) (by rw [mul_comm]; exact hpq)
  have cplx : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ aeval (a : ℂ) (X ^ 4 - X ^ 2 - 1 : ℚ[X]) = 0 ∧
      aeval ((b : ℂ) * Complex.I) (X ^ 4 - X ^ 2 - 1 : ℚ[X]) = 0 := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h5' : 1 < Real.sqrt 5 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have A : ∀ x : ℝ, x ^ 2 = (1 + Real.sqrt 5) / 2 → x ^ 4 - x ^ 2 - 1 = 0 := by
      intro x hx
      have : x ^ 4 = (x ^ 2) ^ 2 := by ring
      rw [this, hx]; nlinarith
    have B : ∀ x : ℝ, x ^ 2 = (Real.sqrt 5 - 1) / 2 → x ^ 4 + x ^ 2 - 1 = 0 := by
      intro x hx
      have : x ^ 4 = (x ^ 2) ^ 2 := by ring
      rw [this, hx]; nlinarith
    refine ⟨Real.sqrt ((1 + Real.sqrt 5) / 2), Real.sqrt ((Real.sqrt 5 - 1) / 2), ?_, ?_, ?_, ?_⟩
    · apply Real.sqrt_pos.mpr; linarith
    · apply Real.sqrt_pos.mpr; linarith
    · have ha : Real.sqrt ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 := Real.sq_sqrt (by linarith)
      simp only [map_sub, map_pow, aeval_X, map_one]
      exact_mod_cast A _ ha
    · have hb : Real.sqrt ((Real.sqrt 5 - 1) / 2) ^ 2 = (Real.sqrt 5 - 1) / 2 := Real.sq_sqrt (by linarith)
      simp only [map_sub, map_pow, aeval_X, map_one]
      have := B _ hb
      generalize Real.sqrt ((Real.sqrt 5 - 1) / 2) = y at this
      have h2 : ((y : ℂ) * Complex.I) ^ 4 - ((y : ℂ) * Complex.I) ^ 2 - 1
          = ((y ^ 4 + y ^ 2 - 1 : ℝ) : ℂ) := by
        push_cast
        rw [mul_pow, mul_pow, Complex.I_pow_four, Complex.I_sq]; ring
      rw [h2, this]; simp
  have field_main : ∀ (p : ℚ[X]), p = X ^ 4 - X ^ 2 - 1 →
      ∃ χ : (p.SplittingField ≃ₐ[ℚ] p.SplittingField) →* Equiv.Perm (Fin 4), Function.Injective χ ∧
      (∀ g, χ g * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * χ g) ∧
      8 ≤ Nat.card (p.SplittingField ≃ₐ[ℚ] p.SplittingField) := by
    intro p hp
    have hirr : Irreducible p := hp ▸ f_irred
    have hsep : p.Separable := hirr.separable
    have hdeg : p.natDegree = 4 := by rw [hp]; compute_degree!
    have hne : p ≠ 0 := hirr.ne_zero
    have hsp : (p.map (algebraMap ℚ p.SplittingField)).Splits := SplittingField.splits p
    haveI : IsSplittingField ℚ p.SplittingField p := Polynomial.IsSplittingField.splittingField p
    haveI : Fact (p.map (algebraMap ℚ p.SplittingField)).Splits := ⟨hsp⟩
    haveI : Normal ℚ p.SplittingField := Normal.of_isSplittingField p
    have hpa : ∀ (L : Type) [Field L] [Algebra ℚ L] (x : L), aeval x p = x ^ 4 - x ^ 2 - 1 := by
      intro L _ _ x; rw [hp]; simp
    obtain ⟨a, b, ha, hb, hza, hzc⟩ := cplx
    rw [← hp] at hza hzc
    let ι : p.SplittingField →ₐ[ℚ] ℂ := IsAlgClosed.lift
    have hmem : ∀ z : ℂ, aeval z p = 0 → ∃ r : p.SplittingField, r ∈ p.rootSet p.SplittingField ∧ ι r = z := by
      intro z hz
      have : z ∈ p.rootSet ℂ := (mem_rootSet).2 ⟨hne, hz⟩
      rw [← Splits.image_rootSet hsp ι] at this
      obtain ⟨r, hr, hrz⟩ := this
      exact ⟨r, hr, hrz⟩
    obtain ⟨ra, hra, hιa⟩ := hmem _ hza
    obtain ⟨rc, hrc, hιc⟩ := hmem _ hzc
    have hneg : ∀ r ∈ p.rootSet p.SplittingField, -r ∈ p.rootSet p.SplittingField := by
      intro r hr
      have h := (mem_rootSet.1 hr).2
      refine mem_rootSet.2 ⟨hne, ?_⟩
      rw [hpa] at h ⊢
      linear_combination h
    let e : Fin 4 → p.SplittingField := ![ra, -ra, rc, -rc]
    have he : ∀ i, e i ∈ p.rootSet p.SplittingField := by
      intro i; fin_cases i
      · exact hra
      · exact hneg _ hra
      · exact hrc
      · exact hneg _ hrc
    let w : Fin 4 → ℂ := ![(a : ℂ), -(a : ℂ), (b : ℂ) * Complex.I, -((b : ℂ) * Complex.I)]
    have hw : ∀ i, ι (e i) = w i := by
      intro i; fin_cases i <;> simp [e, w, hιa, hιc]
    have winj : Function.Injective w := by
      intro i j h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      fin_cases i <;> fin_cases j <;> simp [w] at hre him h ⊢ <;> linarith
    have einj : Function.Injective e := by
      intro i j h
      apply winj
      rw [← hw, ← hw, h]
    let e' : Fin 4 → ↥(p.rootSet p.SplittingField) := fun i => ⟨e i, he i⟩
    have e'inj : Function.Injective e' := fun i j h => einj (congrArg Subtype.val h)
    have e'bij : Function.Bijective e' := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨e'inj, ?_⟩
      rw [card_rootSet_eq_natDegree hsep hsp, hdeg]; simp
    let ε : Fin 4 ≃ ↥(p.rootSet p.SplittingField) := Equiv.ofBijective e' e'bij
    let χ : (p.SplittingField ≃ₐ[ℚ] p.SplittingField) →* Equiv.Perm (Fin 4) :=
      (Equiv.permCongrHom ε.symm).toMonoidHom.comp ((Gal.galActionHom p p.SplittingField).comp (Gal.restrict p p.SplittingField))
    have key : ∀ g i, e (χ g i) = g (e i) := by
      intro g i
      have h1 : ε (χ g i) = Gal.galActionHom p p.SplittingField (Gal.restrict p p.SplittingField g) (ε i) := by
        simp [χ, Equiv.permCongrHom, Equiv.permCongr_apply]
      have h2 := Gal.galActionHom_restrict p p.SplittingField g (ε i)
      rw [← h1] at h2
      exact h2
    have t0 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 0 = 1 := by decide
    have t1 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 1 = 0 := by decide
    have t2 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 2 = 3 := by decide
    have t3 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 3 = 2 := by decide
    have hτ : ∀ i, e ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i) = - e i := by
      intro i; fin_cases i
      · simp only [Fin.zero_eta, t0]; rfl
      · simp only [Fin.mk_one, t1]; simp [e]
      · simp only [Fin.reduceFinMk, t2]; rfl
      · simp only [Fin.reduceFinMk, t3]; simp [e]
    have hsurj : ∀ r ∈ p.rootSet p.SplittingField, ∃ i, e i = r := by
      intro r hr
      obtain ⟨i, hi⟩ := e'bij.2 ⟨r, hr⟩
      exact ⟨i, congrArg Subtype.val hi⟩
    have χinj : Function.Injective χ := by
      intro g1 g2 h
      have : g1.toAlgHom = g2.toAlgHom := by
        apply AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet p.SplittingField p)
        intro r hr
        obtain ⟨i, rfl⟩ := hsurj r hr
        have := key g1 i
        have h2 := key g2 i
        rw [h] at this
        show g1 (e i) = g2 (e i)
        rw [← this, h2]
      exact AlgEquiv.ext (fun x => by simpa using AlgHom.congr_fun this x)
    have χcomm : ∀ g, χ g * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * χ g := by
      intro g
      refine Equiv.ext fun i => ?_
      apply einj
      show e (χ g ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i)) = e ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) (χ g i))
      rw [key, hτ, hτ, map_neg, key]
    -- conjugation
    obtain ⟨σ, hσ⟩ : ∃ σ : p.SplittingField ≃ₐ[ℚ] p.SplittingField, ∀ x, ι (σ x) = (starRingEnd ℂ) (ι x) := by
      letI : Algebra p.SplittingField ℂ := ι.toRingHom.toAlgebra
      haveI : IsScalarTower ℚ p.SplittingField ℂ := IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
      refine ⟨(Complex.conjAe.restrictScalars ℚ).restrictNormal p.SplittingField, fun x => ?_⟩
      exact AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) p.SplittingField x
    have σa : σ ra = ra := by
      have : ι (σ ra) = ι ra := by rw [hσ, hιa, Complex.conj_ofReal]
      exact ι.injective this
    have σc : σ rc ≠ rc := by
      intro h
      have := hσ rc
      rw [h, hιc] at this
      have := congrArg Complex.im this
      simp at this
      linarith
    refine ⟨χ, χinj, χcomm, ?_⟩
    haveI := Gal.galAction_isPretransitive p p.SplittingField hirr
    let x0 : ↥(p.rootSet p.SplittingField) := ⟨ra, hra⟩
    have hidx := MulAction.index_stabilizer_of_transitive p.Gal x0
    have hR : Nat.card ↥(p.rootSet p.SplittingField) = 4 := by
      rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep hsp, hdeg]
    have hmul := Subgroup.card_mul_index (MulAction.stabilizer p.Gal x0)
    have hst : 2 ≤ Nat.card (MulAction.stabilizer p.Gal x0) := by
      have : 1 < Nat.card (MulAction.stabilizer p.Gal x0) := by
        rw [Finite.one_lt_card_iff_nontrivial]
        refine ⟨⟨⟨Gal.restrict p p.SplittingField σ, ?_⟩, 1, ?_⟩⟩
        · rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          have := Gal.galActionHom_restrict p p.SplittingField σ x0
          exact this.trans σa
        · intro h
          have h1 : Gal.restrict p p.SplittingField σ = 1 := congrArg Subtype.val h
          have := Gal.galActionHom_restrict p p.SplittingField σ ⟨rc, hrc⟩
          rw [h1, map_one] at this
          exact σc this.symm
      omega
    have h8 : 8 ≤ Nat.card p.Gal := by
      rw [← hmul, hidx, hR]; omega
    exact le_trans h8 (Nat.card_le_card_of_surjective _ (Gal.restrict_surjective p p.SplittingField))
  have hK : IsGalois ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField :=
    haveI := Polynomial.IsSplittingField.splittingField (X ^ 4 - X ^ 2 - 1 : ℚ[X])
    IsGalois.of_separable_splitting_field f_irred.separable
  have step1 := Nat.card_congr (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField)).toEquiv
  rw [step1]
  obtain ⟨χ, h1, h2, h3⟩ := field_main _ rfl
  haveI : Finite ((X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField ≃ₐ[ℚ] (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField) := inferInstance
  exact grp_main _ χ h1 h2 h3
