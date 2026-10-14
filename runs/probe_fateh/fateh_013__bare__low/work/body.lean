  have hpp : p.Prime := Fact.out
  obtain ⟨ut, hut⟩ : ∃ ut : ZMod p → GL (Fin 2) (ZMod p), ∀ a, (ut a).1 = !![1,a;0,1] := by
    refine ⟨fun a => ⟨!![1,a;0,1], !![1,-a;0,1], ?_, ?_⟩, fun a => rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨mk, hmk⟩ : ∃ mk : (ZMod p)ˣ → (ZMod p)ˣ → ZMod p → GL (Fin 2) (ZMod p),
      ∀ a d b, (mk a d b).1 = !![(a : ZMod p), b; 0, d] := by
    refine ⟨fun a d b => ⟨!![(a : ZMod p), b; 0, d], !![((a⁻¹ : (ZMod p)ˣ) : ZMod p), -(a⁻¹ : (ZMod p)ˣ) * b * (d⁻¹ : (ZMod p)ˣ); 0, ((d⁻¹ : (ZMod p)ˣ) : ZMod p)], ?_, ?_⟩, fun a d b => rfl⟩
    · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      simp only [mul_zero, zero_mul, add_zero, zero_add, Units.mul_inv]
      have h : (a : ZMod p) * (-(a⁻¹ : (ZMod p)ˣ) * b * (d⁻¹ : (ZMod p)ˣ)) + b * (d⁻¹ : (ZMod p)ˣ) = 0 := by
        linear_combination (-(b * ((d⁻¹ : (ZMod p)ˣ) : ZMod p))) * a.mul_inv
      rw [h]
    · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      simp only [mul_zero, zero_mul, add_zero, zero_add, Units.inv_mul]
      have h : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b + -(a⁻¹ : (ZMod p)ˣ) * b * (d⁻¹ : (ZMod p)ˣ) * d = 0 := by
        linear_combination (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b) * (-(d.inv_mul))
      rw [h]
  have hmul : ∀ a b, ut (a+b) = ut a * ut b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hut, hut, hut]
    rw [Matrix.mul_fin_two]
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
    rw [add_comm]
  have hinj : Function.Injective ut := by
    intro a b h
    have := congrArg (fun g : GL (Fin 2) (ZMod p) => g.1 0 1) h
    simpa [hut] using this
  have h0 : ut 0 = 1 := by
    apply Units.ext
    rw [hut]; ext i j; fin_cases i <;> fin_cases j <;> simp
  let φ : Multiplicative (ZMod p) →* GL (Fin 2) (ZMod p) :=
    { toFun := fun a => ut a.toAdd, map_one' := h0, map_mul' := fun a b => hmul _ _ }
  have φinj : Function.Injective φ := fun a b h => hinj h
  let U := φ.range
  have hU : Nat.card U = p := by
    have h2 : Nat.card U = Nat.card (Multiplicative (ZMod p)) := (Nat.card_congr (Equiv.ofInjective φ φinj)).symm
    rw [h2]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have key : ∀ a d b t, mk a d b * ut t = ut ((a:ZMod p) * t * (d⁻¹ : (ZMod p)ˣ)) * mk a d b := by
    intro a d b t
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hut, hut, hmk]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
    have h : (a : ZMod p) * t * (d⁻¹ : (ZMod p)ˣ) * d = a * t := by
      rw [mul_assoc, d.inv_mul, mul_one]
    rw [h, add_comm]
  have memU : ∀ t, ut t ∈ U := fun t => ⟨Multiplicative.ofAdd t, rfl⟩
  have hNsub : ∀ g ∈ (Subgroup.normalizer (U : Set (GL (Fin 2) (ZMod p)))), g.1 1 0 = 0 := by
    intro g hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hg (ut 1)).mp (memU 1)
    obtain ⟨y, hy⟩ := h1
    have h2 : ut y.toAdd * g = g * ut 1 := by
      have : g * ut 1 = φ y * g := (mul_inv_eq_iff_eq_mul.mp hy.symm)
      exact this.symm
    have h3 := congrArg (fun g : GL (Fin 2) (ZMod p) => g.1 1 1) h2
    simpa [hut, Matrix.mul_apply, Fin.sum_univ_two] using h3
  have hNmem : ∀ a d b, mk a d b ∈ (Subgroup.normalizer (U : Set (GL (Fin 2) (ZMod p)))) := by
    intro a d b
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, rfl⟩
      have e : mk a d b * φ x * (mk a d b)⁻¹ = ut ((a:ZMod p) * x.toAdd * (d⁻¹ : (ZMod p)ˣ)) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact key a d b x.toAdd
      rw [e]; exact memU _
    · rintro ⟨y, hy⟩
      have e1 : mk a d b * h = φ y * mk a d b := mul_inv_eq_iff_eq_mul.mp hy.symm
      have ha := a.mul_inv
      have hd := d.mul_inv
      have e : (a : ZMod p) * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * y.toAdd * d) * (d⁻¹ : (ZMod p)ˣ) = y.toAdd := by
        linear_combination (y.toAdd * (d : ZMod p) * ((d⁻¹ : (ZMod p)ˣ) : ZMod p)) * ha + y.toAdd * hd
      have e2 := key a d b (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * y.toAdd * d)
      rw [e] at e2
      have : h = ut (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * y.toAdd * d) := by
        apply mul_left_cancel (a := mk a d b)
        rw [e1, e2]; rfl
      rw [this]; exact memU _
  have hdetne : ∀ g : GL (Fin 2) (ZMod p), g.1 1 0 = 0 → g.1 0 0 ≠ 0 ∧ g.1 1 1 ≠ 0 := by
    intro g hc
    have hu : IsUnit g.1.det := (Matrix.GeneralLinearGroup.det g).isUnit
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hu
    have := hu.ne_zero
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  have hGc : Nat.card (GL (Fin 2) (ZMod p)) = p * ((p-1)*(p-1)*(p+1)) := by
    rw [Matrix.card_GL_field]
    simp only [Fin.prod_univ_two, ZMod.card]
    have hp := (Fact.out : p.Prime).pos
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have e1 : (q+1)^2-(q+1)^0 = q*(q+2) := by apply Nat.sub_eq_of_eq_add; ring
    have e2 : (q+1)^2-(q+1)^(1:ℕ) = q*(q+1) := by apply Nat.sub_eq_of_eq_add; ring
    have e3 : q+1-1 = q := by omega
    simp only [Fin.val_zero, Fin.val_one, e1, e2, e3]
    ring
  have hNc : Nat.card (Subgroup.normalizer (U : Set (GL (Fin 2) (ZMod p)))) = p * ((p-1)*(p-1)) := by
    have hT : Nat.card ((ZMod p)ˣ × (ZMod p)ˣ × ZMod p) = p * ((p-1)*(p-1)) := by
      rw [Nat.card_prod, Nat.card_prod]
      simp only [Nat.card_eq_fintype_card, ZMod.card_units, ZMod.card]
      ring
    rw [← hT]
    apply le_antisymm
    · refine Nat.card_le_card_of_injective
        (fun g => (Units.mk0 (g.1.1 0 0) (hdetne g.1 (hNsub g.1 g.2)).1,
                   Units.mk0 (g.1.1 1 1) (hdetne g.1 (hNsub g.1 g.2)).2, g.1.1 0 1)) ?_
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
      simp only [Prod.mk.injEq, Units.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      apply Subtype.ext
      apply Units.ext
      have c1 := hNsub g hg
      have c2 := hNsub g' hg'
      have h1' : g.1 0 0 = g'.1 0 0 := by simpa using congrArg Units.val h1
      have h2' : g.1 1 1 = g'.1 1 1 := by simpa using congrArg Units.val h2
      ext i j; fin_cases i <;> fin_cases j <;> simpa [c1, c2] using (by assumption)
    · refine Nat.card_le_card_of_injective
        (fun x : (ZMod p)ˣ × (ZMod p)ˣ × ZMod p => (⟨mk x.1 x.2.1 x.2.2, hNmem _ _ _⟩ : Subgroup.normalizer (U : Set (GL (Fin 2) (ZMod p))))) ?_
      rintro ⟨a, d, b⟩ ⟨a', d', b'⟩ h
      have := congrArg (fun g : Subgroup.normalizer (U : Set (GL (Fin 2) (ZMod p))) => g.1.1) h
      simp only [hmk] at this
      have h00 : (a : ZMod p) = a' := congrFun (congrFun this 0) 0
      have h11 : (d : ZMod p) = d' := congrFun (congrFun this 1) 1
      have h01 : b = b' := congrFun (congrFun this 0) 1
      rw [Units.ext h00, Units.ext h11, h01]
  have hex : ∃ P : Sylow p (GL (Fin 2) (ZMod p)), U ≤ P := by
    apply IsPGroup.exists_le_sylow
    exact IsPGroup.of_card (by rw [hU, pow_one])
  obtain ⟨P, hP⟩ := hex
  have hm : ¬ p ∣ (p-1)*(p-1)*(p+1) := by

    intro hd
    have h2 := hpp.two_le
    rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hpp).mp h with h | h <;>
      · have := Nat.le_of_dvd (by omega) h; omega
    · have := (Nat.dvd_add_right (dvd_refl p)).mp h
      have := Nat.le_of_dvd (by omega) this; omega
  have hm0 : (p-1)*(p-1)*(p+1) ≠ 0 := by
    apply Nat.pos_iff_ne_zero.mp
    have : 0 < p-1 := by have := hpp.two_le; omega
    positivity
  have hPc : Nat.card P = p := by
    rw [Sylow.card_eq_multiplicity, hGc, Nat.factorization_mul hpp.ne_zero hm0]
    simp [hpp.factorization, Nat.factorization_eq_zero_of_not_dvd hm]
  have heq : (P : Subgroup (GL (Fin 2) (ZMod p))) = U :=
    (Subgroup.eq_of_le_of_card_ge hP (by rw [hPc, hU])).symm
  have heq' : (P : Set (GL (Fin 2) (ZMod p))) = (U : Set (GL (Fin 2) (ZMod p))) := by
    ext x; exact SetLike.ext_iff.mp heq x
  rw [Sylow.card_eq_index_normalizer P, heq']
  have h := Subgroup.index_mul_card (Subgroup.normalizer (U : Set (GL (Fin 2) (ZMod p))))
  rw [hNc, hGc] at h
  have hpos : 0 < p * ((p-1)*(p-1)) := by
    have := hpp.two_le
    have : 0 < p-1 := by omega
    positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]; ring
