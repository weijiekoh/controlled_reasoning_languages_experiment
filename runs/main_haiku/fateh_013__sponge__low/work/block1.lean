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
  sorry
