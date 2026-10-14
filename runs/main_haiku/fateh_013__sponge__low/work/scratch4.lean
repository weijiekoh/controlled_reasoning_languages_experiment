import Mathlib

open Matrix

/--
Prove that the number of Sylow $p$-subgroups of $\operatorname{GL}_2(\mathbb{F}_p)$ is $p + 1$.
-/
theorem card_sylow_gl_two_eq_add_one (p : ℕ) [Fact p.Prime] :
    Nat.card (Sylow p <| GL (Fin 2) (ZMod p)) = p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  -- order of GL_2(F_p)
  have hG : Nat.card (GL (Fin 2) (ZMod p)) = p * ((p - 1) ^ 2 * (p + 1)) := by
    rw [card_GL_field 2, ZMod.card]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have e1 : (q + 2) ^ 2 - 1 = (q + 1) * (q + 3) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring
    have e2 : (q + 2) ^ 2 - (q + 2) = (q + 2) * (q + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring
    have e3 : q + 2 - 1 = q + 1 := by omega
    rw [e1, e2, e3]; ring
  -- the upper unipotent subgroup U
  let U : Subgroup (GL (Fin 2) (ZMod p)) :=
    { carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 ∧
          (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0}
      mul_mem' := by
        rintro a b ⟨a0, a1, a2⟩ ⟨b0, b1, b2⟩
        refine ⟨?_, ?_, ?_⟩ <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, a0, a1, a2, b0, b1, b2]
      one_mem' := by simp
      inv_mem' := by
        rintro a ⟨a0, a1, a2⟩
        have h2 : ((a⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * (a : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := Units.inv_mul a
        have e00 := congrFun (congrFun h2 0) 0
        have e10 := congrFun (congrFun h2 1) 0
        have e11 := congrFun (congrFun h2 1) 1
        simp [Matrix.mul_apply, Fin.sum_univ_two, a0, a1, a2] at e00 e10
        simp [Matrix.mul_apply, Fin.sum_univ_two, a0, a1, a2, e10] at e11
        exact ⟨by simpa using e00, by simpa using e11, by simpa using e10⟩ }
  -- explicit elements
  let uni : ZMod p → GL (Fin 2) (ZMod p) := fun t =>
    ⟨!![1, t; 0, 1], !![1, -t; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
      by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  have huni_mem : ∀ t, uni t ∈ U := fun t => by
    refine ⟨?_, ?_, ?_⟩ <;> simp [uni]
  have hU : Nat.card U = p := by
    refine Eq.trans ?_ (Nat.card_zmod p)
    apply Nat.card_congr
    exact
      { toFun := fun g => (g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1
        invFun := fun t => ⟨uni t, huni_mem t⟩
        left_inv := by
          rintro ⟨g, g0, g1, g2⟩
          apply Subtype.ext
          apply Units.ext
          ext i j
          fin_cases i <;> fin_cases j <;> simp [uni, g0, g1, g2]
        right_inv := by
          intro t
          simp [uni] }
  have hUp : IsPGroup p U := IsPGroup.of_card (n := 1) (by rw [hU, pow_one])
  -- the order of G has p-part exactly p
  have hpnd : ∀ k, p ^ k ∣ p * ((p - 1) ^ 2 * (p + 1)) → k ≤ 1 := by
    intro k hk
    by_contra hk2
    have hk3 : 2 ≤ k := by omega
    have h2 : p ^ 2 ∣ p * ((p - 1) ^ 2 * (p + 1)) := (pow_dvd_pow p hk3).trans hk
    rw [pow_two] at h2
    have h3 : p ∣ (p - 1) ^ 2 * (p + 1) := Nat.dvd_of_mul_dvd_mul_left hp.pos h2
    rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
    · have h5 : p ∣ p - 1 := hp.dvd_of_dvd_pow h4
      have := Nat.le_of_dvd (by omega) h5
      omega
    · have h5 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h4
      have := Nat.le_of_dvd (by norm_num) h5
      omega
  have hmax : ∀ {Q : Subgroup (GL (Fin 2) (ZMod p))}, IsPGroup p Q → U ≤ Q → Q = U := by
    intro Q hQ hUQ
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ
    have hdvd : Nat.card Q ∣ Nat.card (GL (Fin 2) (ZMod p)) := Subgroup.card_subgroup_dvd_card Q
    rw [hk, hG] at hdvd
    have hk1 := hpnd k hdvd
    have hle : Nat.card Q ≤ Nat.card U := by
      rw [hk, hU]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
        _ = p := pow_one p
    exact (Subgroup.eq_of_le_of_card_ge hUQ hle).symm
  let S0 : Sylow p (GL (Fin 2) (ZMod p)) := ⟨U, hUp, fun hQ hUQ => hmax hQ hUQ⟩
  let S0 : Sylow p (GL (Fin 2) (ZMod p)) := ⟨U, hUp, fun hQ hUQ => hmax hQ hUQ⟩
  -- entries of inverses of Borel-type elements
  have hinv : ∀ g : GL (Fin 2) (ZMod p), (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 →
      ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 ∧
      ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 ∧
      ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
    intro g hg
    have h2 : ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := Units.inv_mul g
    have e00 : ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hg] using congrFun (congrFun h2 0) 0
    have e10 : ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hg] using congrFun (congrFun h2 1) 0
    have hx10 : ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
      calc ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0
          = ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 *
              (((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) := by
            rw [e00, mul_one]
        _ = (((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) *
              ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 := by ring
        _ = 0 := by rw [e10, zero_mul]
    have e11 : ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
      have e := congrFun (congrFun h2 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hx10, zero_mul, zero_add] at e
      exact e
    exact ⟨hx10, e00, e11⟩
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
