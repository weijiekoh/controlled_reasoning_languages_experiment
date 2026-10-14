  -- conjugation by a lower-left-zero element preserves U
  have hFw : ∀ g : GL (Fin 2) (ZMod p), (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 →
      ∀ h ∈ U, g * h * g⁻¹ ∈ U := by
    intro g hg h hh
    obtain ⟨hx10, e00, e11⟩ := hinv g hg
    obtain ⟨h00, h11, h10⟩ := hh
    refine ⟨?_, ?_, ?_⟩
    · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h00, h11, h10, hg, hx10]
      linear_combination e00
    · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h00, h11, h10, hg, hx10]
      linear_combination e11
    · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h00, h11, h10, hg, hx10]
      ring
  -- the Borel subgroup
  let B : Subgroup (GL (Fin 2) (ZMod p)) :=
    { carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0}
      mul_mem' := by
        intro a b ha hb
        have ha' : (a : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := ha
        have hb' : (b : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := hb
        show ((a * b : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0
        simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha', hb', mul_zero, zero_mul, add_zero, zero_add]
      one_mem' := by
        show ((1 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0
        simp
      inv_mem' := fun {a} ha => (hinv a ha).1 }
  -- the normalizer of U is B
  have hNB : Subgroup.normalizer (U : Set (GL (Fin 2) (ZMod p))) = B := by
    ext g
    rw [Subgroup.mem_normalizer_iff]
    constructor
    · intro hN
      show (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0
      obtain ⟨k, hk⟩ : ∃ k, k = g * uni 1 * g⁻¹ := ⟨_, rfl⟩
      have hkU : k ∈ U := by rw [hk]; exact (hN (uni 1)).mp (huni_mem 1)
      obtain ⟨k00, k11, k10⟩ := hkU
      have hid : k * g = g * uni 1 := by rw [hk]; group
      have e := congrFun (congrFun (congrArg Units.val hid) 1) 1
      simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, uni, k10, k11] at e
      first
        | exact e
        | linear_combination e
        | linear_combination -e
    · intro hg
      have hg' : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := hg
      intro h
      constructor
      · exact fun hh => hFw g hg' h hh
      · intro hm
        have := hFw g⁻¹ (hinv g hg').1 (g * h * g⁻¹) hm
        convert this using 1
        group
  -- the order of B
  have hBcard : Nat.card B = p * (p - 1) ^ 2 := by
    have hu : Nat.card (ZMod p)ˣ = p - 1 := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
    have hz : Nat.card (ZMod p) = p := Nat.card_zmod p
    have key : ∀ a b c : ZMod p, a ≠ 0 → b ≠ 0 →
        (!![a, c; 0, b] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![a⁻¹, -a⁻¹ * c * b⁻¹; 0, b⁻¹] = 1 ∧
        (!![a⁻¹, -a⁻¹ * c * b⁻¹; 0, b⁻¹] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![a, c; 0, b] = 1 := by
      intro a b c ha hb
      constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring)
    let mkG : (ZMod p)ˣ × (ZMod p)ˣ × ZMod p → GL (Fin 2) (ZMod p) := fun x =>
      ⟨!![(x.1 : ZMod p), x.2.2; 0, (x.2.1 : ZMod p)],
        !![(x.1 : ZMod p)⁻¹, -(x.1 : ZMod p)⁻¹ * x.2.2 * (x.2.1 : ZMod p)⁻¹; 0, (x.2.1 : ZMod p)⁻¹],
        (key _ _ _ (Units.ne_zero x.1) (Units.ne_zero x.2.1)).1,
        (key _ _ _ (Units.ne_zero x.1) (Units.ne_zero x.2.1)).2⟩
    let f : (ZMod p)ˣ × (ZMod p)ˣ × ZMod p → B := fun x =>
      ⟨mkG x, by
        show ((mkG x : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0
        simp [mkG]⟩
    have hinj : Function.Injective f := by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ hxy
      have h1 := congrArg (fun z : B => ((z : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) hxy
      have h2 := congrArg (fun z : B => ((z : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1) hxy
      have h3 := congrArg (fun z : B => ((z : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) hxy
      simp [f, mkG] at h1 h2 h3
      have ha : a = a' := Units.ext h1
      have hb : b = b' := Units.ext h2
      subst ha; subst hb; subst h3; rfl
    have hsurj : Function.Surjective f := by
      rintro ⟨g, hg⟩
      have hg' : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := hg
      obtain ⟨_, e00, e11⟩ := hinv g hg'
      have n0 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ≠ 0 := by
        intro h; rw [h, mul_zero] at e00; exact zero_ne_one e00
      have n1 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 ≠ 0 := by
        intro h; rw [h, mul_zero] at e11; exact zero_ne_one e11
      refine ⟨(Units.mk0 _ n0, Units.mk0 _ n1, (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1), ?_⟩
      apply Subtype.ext
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [f, mkG, hg']
    rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩, Nat.card_prod, Nat.card_prod, hu, hz]
    ring
  -- conclude
  have hidx : Nat.card (Sylow p (GL (Fin 2) (ZMod p))) = B.index := by
    rw [Sylow.card_eq_index_normalizer S0]
    congr 1
  have hc := Subgroup.card_mul_index B
  rw [hBcard, hG] at hc
  have hpos : 0 < p * (p - 1) ^ 2 := Nat.mul_pos (by omega) (pow_pos (by omega) 2)
  have h4 : p * (p - 1) ^ 2 * B.index = p * (p - 1) ^ 2 * (p + 1) := by rw [hc]; ring
  rw [hidx]
  exact Nat.eq_of_mul_eq_mul_left hpos h4
