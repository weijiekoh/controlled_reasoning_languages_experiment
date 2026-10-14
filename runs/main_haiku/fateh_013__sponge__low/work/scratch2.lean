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
  sorry
