
def Mf {m : ℕ} (f : Fin m × Fin m → Bool) : Matrix (Fin m) (Fin m) ℝ := fun i j => vv (f (i, j))

lemma sumdet (n : ℕ) (hn : 1 ≤ n) :
    (∑ f : Fin (2*n) × Fin (2*n) → Bool, (Mf f - (Mf f).transpose).det) =
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (2*n)) => σ.cycleType = Multiset.replicate n 2)).card : ℝ)
        * (2 ^ ((2*n) * (2*n)) * (1/2 : ℝ) ^ n) := by
  have h1 : ∀ f : Fin (2*n) × Fin (2*n) → Bool, (Mf f - (Mf f).transpose).det =
      ∑ σ : Equiv.Perm (Fin (2*n)), (σ.sign : ℝ) * ∏ i, hh σ i f := by
    intro f
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl; intro σ _
    simp [Units.smul_def, zsmul_eq_mul, hh, Mf, Matrix.sub_apply]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h2 : ∀ σ : Equiv.Perm (Fin (2*n)), (σ.sign : ℝ) * ∑ f : Fin (2*n) × Fin (2*n) → Bool, ∏ i, hh σ i f
      = if σ.cycleType = Multiset.replicate n 2 then 2 ^ ((2*n) * (2*n)) * (1/2 : ℝ) ^ n else 0 := by
    intro σ
    split_ifs with hc
    · have hP := (char_inv n σ).mpr hc
      rw [inv_case σ (fun i => (hP i).1) (fun i => (hP i).2) n Finset.univ (by simp [two_mul]) (by simp)]
      have : (σ.sign : ℝ) = (-1) ^ n := by
        rw [Equiv.Perm.sign_of_cycleType, hc]
        simp
        rw [pow_add, pow_mul]; simp; exact neg_one_pow_eq_or ℝ n
      rw [this]
      have : ((-1:ℝ)^n) * (-1/2)^n = (1/2)^n := by
        rw [← mul_pow]; norm_num
      calc (-1:ℝ)^n * (2 ^ ((2*n)*(2*n)) * (-1/2)^n) = 2 ^ ((2*n)*(2*n)) * ((-1:ℝ)^n * (-1/2)^n) := by ring
        _ = _ := by rw [this]
    · rw [zero_case σ, mul_zero]
      intro hP; exact hc ((char_inv n σ).mp hP)
  simp only [h2]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  simp
