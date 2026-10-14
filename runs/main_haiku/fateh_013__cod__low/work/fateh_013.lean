import Mathlib

open Matrix

/--
Prove that the number of Sylow $p$-subgroups of $\operatorname{GL}_2(\mathbb{F}_p)$ is $p + 1$.
-/
theorem card_sylow_gl_two_eq_add_one (p : ℕ) [Fact p.Prime] :
    Nat.card (Sylow p <| GL (Fin 2) (ZMod p)) = p + 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 :=
    ⟨p - 2, by have := (Fact.out : (p).Prime).two_le; omega⟩
  -- entry relations for g with g 1 0 = 0
  have hrel : ∀ g : GL (Fin 2) (ZMod (q+2)),
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0 →
      ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 0 *
        ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 0 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 1 *
        ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 1 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 0 *
        ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 1 +
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 1 *
        ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 1 = 0 := by
    intro g hg
    have h := Units.mul_inv g
    generalize hH : ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) = H at h ⊢
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hg, Matrix.one_apply, zero_mul, zero_add,
      add_zero, Fin.isValue, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, if_true, if_false,
      one_ne_zero, mul_one] at e00 e01 e10 e11
    norm_num at e01
    have h10 : H 1 0 = 0 := by
      linear_combination (H 1 1) * e10 - (H 1 0) * e11
    refine ⟨h10, ?_, ?_, ?_⟩
    · linear_combination e00 - ((g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 1) * h10
    · linear_combination e11
    · linear_combination e01
  -- the unipotent elements
  let mkU : ZMod (q+2) → GL (Fin 2) (ZMod (q+2)) := fun s =>
    ⟨!![1, s; 0, 1], !![1, -s; 0, 1], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hmkU : ∀ s, ((mkU s : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) = !![1, s; 0, 1] := fun s => rfl
  let U : Subgroup (GL (Fin 2) (ZMod (q+2))) :=
    { carrier := {g | ∃ s : ZMod (q+2), (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) = !![1, s; 0, 1]}
      mul_mem' := by
        rintro a b ⟨s, hs⟩ ⟨t, ht⟩
        refine ⟨s + t, ?_⟩
        rw [Units.val_mul, hs, ht]
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
      one_mem' := ⟨0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
      inv_mem' := by
        rintro a ⟨s, hs⟩
        refine ⟨-s, ?_⟩
        rw [Matrix.coe_units_inv, hs]
        apply Matrix.inv_eq_right_inv
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }
  have hUmem : ∀ g : GL (Fin 2) (ZMod (q+2)), g ∈ U ↔ ∃ s : ZMod (q+2), (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) = !![1, s; 0, 1] := fun g => Iff.rfl
  -- the Borel-type subgroup
  let B : Subgroup (GL (Fin 2) (ZMod (q+2))) :=
    { carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0}
      mul_mem' := by
        intro a b ha hb
        have ha' : (a : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0 := ha
        have hb' : (b : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0 := hb
        show ((a * b : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0
        rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha', hb']
        ring
      one_mem' := by
        show ((1 : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0
        simp
      inv_mem' := fun {a} ha => (hrel a ha).1 }
  have hBmem : ∀ g : GL (Fin 2) (ZMod (q+2)), g ∈ B ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0 := fun g => Iff.rfl
  -- forward conjugation: B normalizes U
  have hfwd : ∀ g : GL (Fin 2) (ZMod (q+2)), g ∈ B → ∀ h ∈ U, g * h * g⁻¹ ∈ U := by
    intro g hg h hh
    obtain ⟨s, hs⟩ := hh
    rw [hBmem] at hg
    rw [hUmem]
    obtain ⟨h10, h00, h11, h01⟩ := hrel g hg
    refine ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 0 * s *
      ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 1, ?_⟩
    rw [Units.val_mul, Units.val_mul, hs]
    generalize ((g⁻¹ : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) = H at h10 h00 h11 h01 ⊢
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hg, h10]
    all_goals first
      | linear_combination h00
      | linear_combination h11
      | linear_combination h01
      | skip
  -- cardinality of U
  have hcardU : Nat.card U = q + 2 := by
    have hbij : Function.Bijective (fun s : ZMod (q+2) => (⟨mkU s, s, rfl⟩ : U)) := by
      constructor
      · intro s t hst
        have h1 := congrArg (fun x : U => (x : GL (Fin 2) (ZMod (q+2))) : U → _) hst
        have h2 := congrFun (congrFun (congrArg (fun x : GL (Fin 2) (ZMod (q+2)) => (x : Matrix (Fin 2) (Fin 2) (ZMod (q+2)))) h1) 0) 1
        simpa [hmkU] using h2
      · rintro ⟨g, s, hs⟩
        exact ⟨s, Subtype.ext (Units.ext hs.symm)⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  -- cardinality of B
  have hcardB : Nat.card B = (q+1) * (q+1) * (q+2) := by
    have hgen : ∀ (a a' d d' b : ZMod (q+2)), a * a' = 1 → d * d' = 1 →
        (!![a, b; 0, d] * !![a', -(b * a' * d'); 0, d'] = 1 ∧
          !![a', -(b * a' * d'); 0, d'] * !![a, b; 0, d] = 1) := by
      intro a a' d d' b hA hD
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        · exact hA
        · linear_combination (-(b*d'))*hA
        · exact hD
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination hA
        · linear_combination (-(b*a'))*hD
        · linear_combination hD
    let mkB : (ZMod (q+2))ˣ × (ZMod (q+2))ˣ × ZMod (q+2) → GL (Fin 2) (ZMod (q+2)) :=
      fun x => ⟨!![(x.1 : ZMod (q+2)), x.2.2; 0, (x.2.1 : ZMod (q+2))],
        !![((x.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2)), -(x.2.2 * ((x.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2)) * ((x.2.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2)));
          0, ((x.2.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2))],
        (hgen _ _ _ _ _ (Units.mul_inv x.1) (Units.mul_inv x.2.1)).1,
        (hgen _ _ _ _ _ (Units.mul_inv x.1) (Units.mul_inv x.2.1)).2⟩
    have hmkB : ∀ x, (mkB x : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0 := fun x => rfl
    have hbij : Function.Bijective (fun x : (ZMod (q+2))ˣ × (ZMod (q+2))ˣ × ZMod (q+2) =>
        (⟨mkB x, hmkB x⟩ : B)) := by
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        · exact hA
        · linear_combination (-(b*d'))*hA
        · exact hD
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination hA
        · linear_combination (-(b*a'))*hD
        · linear_combination hD
    let mkB : (ZMod (q+2))ˣ × (ZMod (q+2))ˣ × ZMod (q+2) → GL (Fin 2) (ZMod (q+2)) :=
      fun x => ⟨!![(x.1 : ZMod (q+2)), x.2.2; 0, (x.2.1 : ZMod (q+2))],
        !![((x.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2)), -(x.2.2 * ((x.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2)) * ((x.2.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2)));
          0, ((x.2.1⁻¹ : (ZMod (q+2))ˣ) : ZMod (q+2))],
        (hgen _ _ _ _ _ (Units.mul_inv x.1) (Units.mul_inv x.2.1)).1,
        (hgen _ _ _ _ _ (Units.mul_inv x.1) (Units.mul_inv x.2.1)).2⟩
    have hmkB : ∀ x, (mkB x : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 0 = 0 := fun x => rfl
    have hbij : Function.Bijective (fun x : (ZMod (q+2))ˣ × (ZMod (q+2))ˣ × ZMod (q+2) =>
        (⟨mkB x, hmkB x⟩ : B)) := by
      constructor
      · rintro ⟨a, d, b⟩ ⟨a', d', b'⟩ hxy
        have h1 := congrArg (fun z : B => ((z : GL (Fin 2) (ZMod (q+2))) : Matrix (Fin 2) (Fin 2) (ZMod (q+2)))) hxy
        have e00 : (a : ZMod (q+2)) = a' := congrFun (congrFun h1 0) 0
        have e11 : (d : ZMod (q+2)) = d' := congrFun (congrFun h1 1) 1
        have e01 : b = b' := congrFun (congrFun h1 0) 1
        simp only [Prod.mk.injEq]
        exact ⟨Units.ext e00, Units.ext e11, e01⟩
      · rintro ⟨g, hg⟩
        obtain ⟨-, h00, h11, -⟩ := hrel g hg
        have ha : (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one h00
        have hd : (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 1 1 ≠ 0 := left_ne_zero_of_mul_eq_one h11
        refine ⟨(Units.mk0 _ ha, Units.mk0 _ hd, (g : Matrix (Fin 2) (Fin 2) (ZMod (q+2))) 0 1), ?_⟩
        apply Subtype.ext
        apply Units.ext
        ext i j; fin_cases i <;> fin_cases j <;> simp [mkB, hg]
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_prod, Nat.card_units, ZMod.card]
  sorry
