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
  have : NeZero p := ⟨by omega⟩
  -- determinant is nonzero, in coordinates
  have hdet : ∀ g : GL (Fin 2) (ZMod p),
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1
        - (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 ≠ 0 := by
    intro g h
    have h2 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 0 := by
      rw [Matrix.det_fin_two]; exact h
    have := congrArg Matrix.det (Units.inv_mul g)
    rw [Matrix.det_mul, h2, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have aux : ∀ (A A' D D' b : ZMod p), A * A' = 1 → A' * A = 1 → D * D' = 1 → D' * D = 1 →
      (!![A, b; 0, D] * !![A', -(b * A' * D'); 0, D'] = (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) ∧
      (!![A', -(b * A' * D'); 0, D'] * !![A, b; 0, D] = 1) := by
    intro A A' D D' b h1 h2 h3 h4
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · exact h1
      · linear_combination (-(b*D')) * h1
      · exact h3
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · exact h2
      · linear_combination (-(b*A')) * h4
      · exact h4
  -- upper triangular matrices built from units
  obtain ⟨mkT, hmkT⟩ : ∃ mkT : (ZMod p)ˣ → (ZMod p)ˣ → ZMod p → GL (Fin 2) (ZMod p),
      ∀ a d b, (mkT a d b : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![(a : ZMod p), b; 0, (d : ZMod p)] := by
    refine ⟨fun a d b => Units.mk (!![(a : ZMod p), b; 0, (d : ZMod p)])
      (!![(↑a⁻¹ : ZMod p), -(b * ↑a⁻¹ * ↑d⁻¹); 0, (↑d⁻¹ : ZMod p)]) ?_ ?_, fun _ _ _ => rfl⟩
    · exact (aux _ _ _ _ _ (Units.mul_inv a) (Units.inv_mul a) (Units.mul_inv d) (Units.inv_mul d)).1
    · exact (aux _ _ _ _ _ (Units.mul_inv a) (Units.inv_mul a) (Units.mul_inv d) (Units.inv_mul d)).2
  -- inverse of an upper triangular matrix
  have hinv : ∀ a : GL (Fin 2) (ZMod p), (a : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 →
      (↑a⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 ∧
      (a : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * (↑a⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 ∧
      (a : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 * (↑a⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
    intro a ha10
    have h11 : (a : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 ≠ 0 := by
      intro h; apply hdet a; rw [ha10, h]; ring
    have e1 := congrFun (congrFun (Units.mul_inv a) 1) 0
    have e2 := congrFun (congrFun (Units.mul_inv a) 0) 0
    have e3 := congrFun (congrFun (Units.mul_inv a) 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
      Matrix.one_apply_eq, ha10] at e1 e2 e3
    have hx : (a : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 * (↑a⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
      linear_combination e1
    have hx10 := (mul_eq_zero.mp hx).resolve_left h11
    refine ⟨hx10, ?_, ?_⟩
    · linear_combination e2 - ((a : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) * hx10
    · linear_combination e3
  -- Borel subgroup
  obtain ⟨B, hB⟩ : ∃ B : Subgroup (GL (Fin 2) (ZMod p)),
      ∀ g, g ∈ B ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
    refine ⟨{ carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0},
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · intro a b ha hb
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    · simp
    · intro a ha
      exact (hinv a ha).1
  -- unitriangular subgroup
  obtain ⟨U, hU⟩ : ∃ U : Subgroup (GL (Fin 2) (ZMod p)),
      ∀ g, g ∈ U ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
    refine ⟨{ carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 ∧
                (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0},
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · intro a b ha hb
      obtain ⟨a1, a2, a3⟩ := ha
      obtain ⟨b1, b2, b3⟩ := hb
      simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      refine ⟨?_, ?_, ?_⟩ <;> simp [a1, a2, a3, b1, b2, b3]
    · simp
    · intro a ha
      obtain ⟨a1, a2, a3⟩ := ha
      obtain ⟨x3, x1, x2⟩ := hinv a a3
      rw [a1, one_mul] at x1
      rw [a2, one_mul] at x2
      exact ⟨x1, x2, x3⟩
  -- conjugation preserves U for g in B
  have hL : ∀ g : GL (Fin 2) (ZMod p), (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 →
      ∀ h ∈ U, g * h * g⁻¹ ∈ U := by
    intro g hg h hh
    obtain ⟨h1, h2, h3⟩ := (hU h).1 hh
    obtain ⟨hx10, hx00, hx11⟩ := hinv g hg
    rw [hU]
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, h1, h2, h3, hx10]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hx00
    · linear_combination hx11
    · ring
  -- normalizer of U is B
  have hN : Subgroup.normalizer (U : Subgroup (GL (Fin 2) (ZMod p))) = B := by
    ext g
    rw [Subgroup.mem_normalizer_iff, hB]
    constructor
    · intro hg
      have hu : mkT 1 1 1 ∈ U := by rw [hU, hmkT]; simp
      have hgu := (hg _).1 hu
      rw [hU] at hgu
      obtain ⟨h00, h11, h10⟩ := hgu
      have hrel0 : g * mkT 1 1 1 * g⁻¹ * g = g * mkT 1 1 1 := by group
      generalize g * mkT 1 1 1 * g⁻¹ = v at h00 h11 h10 hrel0
      have hrel := congrArg (fun x : GL (Fin 2) (ZMod p) => (x : Matrix (Fin 2) (Fin 2) (ZMod p))) hrel0
      simp only [Units.val_mul] at hrel
      have e := congrFun (congrFun hrel 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, hmkT, h10, h11] at e
      exact e
    · intro hg h
      constructor
      · intro hh
        exact hL g hg h hh
      · intro hh
        have := hL g⁻¹ (hinv g hg).1 _ hh
        have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
        rwa [e] at this
  -- U has order p
  have eU : U ≃ ZMod p :=
    { toFun := fun g => (g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1
      invFun := fun t => ⟨mkT 1 1 t, (hU _).2 (by rw [hmkT]; simp)⟩
      left_inv := fun g => by
        obtain ⟨h1, h2, h3⟩ := (hU _).1 g.2
        apply Subtype.ext
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hmkT, h1, h2, h3]
      right_inv := fun t => by simp [hmkT] }
  have hcardU : Nat.card U = p := by
    rw [Nat.card_congr eU, Nat.card_eq_fintype_card, ZMod.card]
  -- B has order p (p-1)^2
  have hnz : ∀ g : B, (g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ≠ 0 ∧
      (g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 ≠ 0 := by
    intro g
    have h10 := (hB _).1 g.2
    constructor
    · intro h; apply hdet g.1; simp [h, h10]
    · intro h; apply hdet g.1; simp [h, h10]
  have eB : B ≃ (ZMod p)ˣ × (ZMod p)ˣ × ZMod p :=
    { toFun := fun g => (Units.mk0 _ (hnz g).1, Units.mk0 _ (hnz g).2,
        (g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1)
      invFun := fun x => ⟨mkT x.1 x.2.1 x.2.2, (hB _).2 (by rw [hmkT]; simp)⟩
      left_inv := fun g => by
        have h10 := (hB _).1 g.2
        apply Subtype.ext
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hmkT, h10]
      right_inv := fun x => by
        obtain ⟨a, d, b⟩ := x
        simp [hmkT] }
  have hcardB : Nat.card B = (p - 1) * ((p - 1) * p) := by
    rw [Nat.card_congr eB, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := (ZMod p)ˣ),
      ZMod.card_units, Nat.card_eq_fintype_card (α := ZMod p), ZMod.card]
  -- order of GL_2(F_p)
  have hG : Nat.card (GL (Fin 2) (ZMod p)) = p * ((p - 1) * (p - 1) * (p + 1)) := by
    rw [card_GL_field]
    simp only [ZMod.card, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have h1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]; ring
    have h2 : p ^ 2 - p = p * (p - 1) := by
      zify [show p ≤ p ^ 2 by nlinarith, show 1 ≤ p by omega]; ring
    rw [h1, h2]; ring
  -- index of B is p + 1
  have hIdx : Nat.card (GL (Fin 2) (ZMod p) ⧸ B) = p + 1 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup B
    rw [hG, hcardB] at h
    have hpos : 0 < (p - 1) * ((p - 1) * p) := by
      have : 0 < p - 1 := by omega
      positivity
    have h' : (p + 1) * ((p - 1) * ((p - 1) * p)) = Nat.card (GL (Fin 2) (ZMod p) ⧸ B) * ((p - 1) * ((p - 1) * p)) := by
      rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h'.symm
  -- U is a Sylow p-subgroup
  have hnd : ¬ p ∣ (p - 1) * (p - 1) * (p + 1) := by
    intro h
    rcases hp.dvd_mul.1 h with h' | h'
    · rcases hp.dvd_mul.1 h' with h'' | h'' <;> (have := Nat.le_of_dvd (by omega) h''; omega)
    · have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).1 h'
      have := Nat.le_of_dvd one_pos h1
      omega
  have hUpg : IsPGroup p U := IsPGroup.of_card (n := 1) (by rw [hcardU, pow_one])
  have hmax : ∀ {Q : Subgroup (GL (Fin 2) (ZMod p))}, IsPGroup p Q → U ≤ Q → Q = U := by
    intro Q hQ hUQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hdvdG : Nat.card Q ∣ Nat.card (GL (Fin 2) (ZMod p)) := Subgroup.card_subgroup_dvd_card Q
    have hdvdU : Nat.card U ∣ Nat.card Q := Subgroup.card_dvd_of_le hUQ
    rw [hn, hG] at hdvdG
    rw [hn, hcardU] at hdvdU
    have hn1 : n ≤ 1 := by
      by_contra hc
      have h2 : p ^ 2 ∣ p * ((p - 1) * (p - 1) * (p + 1)) :=
        (pow_dvd_pow p (by omega : 2 ≤ n)).trans hdvdG
      rw [pow_two] at h2
      exact hnd ((Nat.mul_dvd_mul_iff_left hp.pos).1 h2)
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hdvdU
      exact hp.not_dvd_one hdvdU
    have hc : Nat.card Q ≤ Nat.card U := by
      rw [hn, hcardU, show n = 1 by omega, pow_one]
    exact (Subgroup.eq_of_le_of_card_ge hUQ hc).symm
  rw [Sylow.card_eq_card_quotient_normalizer (⟨U, hUpg, fun {Q} hQ hle => hmax hQ hle⟩ : Sylow p (GL (Fin 2) (ZMod p)))]
  show Nat.card (GL (Fin 2) (ZMod p) ⧸ Subgroup.normalizer (U : Subgroup (GL (Fin 2) (ZMod p)))) = p + 1
  rw [hN]
  exact hIdx
