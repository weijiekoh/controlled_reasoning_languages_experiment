import Mathlib

/--
If \( n \) is odd and \( n \geq 3 \), show that the identity is the only element of
\( D_{2n} \) which commutes with all elements of \( D_{2n} \).
-/
theorem DihedralGroup.centralizer_eq_bot {n : ℕ} (hn : Odd n) (h : n ≥ 3) :
    Subgroup.centralizer ⊤ = (⊥ : Subgroup (DihedralGroup n)) := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  have h1 : ((2 * k + 2 : ℕ) : ZMod (2 * k + 1)) = 1 := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  have h2 : ((2 : ℕ) : ZMod (2 * k + 1)) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by norm_num) h0
    omega
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_bot]
  constructor
  · intro hx
    cases x with
    | r i =>
      have hs := hx (DihedralGroup.sr 0) (Subgroup.mem_top _)
      rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at hs
      have hs2 := DihedralGroup.sr.inj hs
      have hi : i + i = 0 := by linear_combination hs2
      have hz : ((2 * k + 2 : ℕ) : ZMod (2 * k + 1)) * i = ((k + 1 : ℕ) : ZMod (2 * k + 1)) * (i + i) := by
        push_cast; ring
      rw [h1, one_mul, hi, mul_zero] at hz
      rw [hz]
      rfl
    | sr j =>
      have hs := hx (DihedralGroup.r 1) (Subgroup.mem_top _)
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at hs
      have hs2 := DihedralGroup.sr.inj hs
      exfalso
      apply h2
      linear_combination -hs2
  · intro hx
    subst hx
    intro g _
    simp
