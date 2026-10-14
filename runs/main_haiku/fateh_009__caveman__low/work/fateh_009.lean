import Mathlib

/--
If \( n \) is odd and \( n \geq 3 \), show that the identity is the only element of
\( D_{2n} \) which commutes with all elements of \( D_{2n} \).
-/
theorem DihedralGroup.centralizer_eq_bot {n : ℕ} (hn : Odd n) (h : n ≥ 3) :
    Subgroup.centralizer ⊤ = (⊥ : Subgroup (DihedralGroup n)) := by
  obtain ⟨m, rfl⟩ := hn
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_bot]
  constructor
  · intro hx
    have h2 : (2 * (m + 1) : ZMod (2 * m + 1)) = 1 := by
      have : ((2 * m + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := ZMod.natCast_self _
      push_cast at this
      linear_combination this
    have h2z : (2 : ZMod (2 * m + 1)) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod (2 * m + 1)) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    cases x with
    | r i =>
      have h1 := hx (sr 0) (Subgroup.mem_top _)
      simp at h1
      have hi : i + i = 0 := by linear_combination h1
      have hi0 : i = 0 := by linear_combination (-i) * h2 + (m + 1) * hi
      rw [hi0]
      rfl
    | sr i =>
      have h1 := hx (r 1) (Subgroup.mem_top _)
      simp at h1
      exfalso
      apply h2z
      linear_combination (-1 : ZMod (2 * m + 1)) * h1
  · rintro rfl
    intro g _
    rw [one_mul, mul_one]
