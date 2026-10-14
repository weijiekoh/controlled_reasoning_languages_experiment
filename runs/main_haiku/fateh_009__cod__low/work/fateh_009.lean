import Mathlib

/--
If \( n \) is odd and \( n \geq 3 \), show that the identity is the only element of
\( D_{2n} \) which commutes with all elements of \( D_{2n} \).
-/
theorem DihedralGroup.centralizer_eq_bot {n : ℕ} (hn : Odd n) (h : n ≥ 3) :
    Subgroup.centralizer ⊤ = (⊥ : Subgroup (DihedralGroup n)) := by
  ext x
  rw [Subgroup.mem_bot, Subgroup.mem_centralizer_iff]
  obtain ⟨m, rfl⟩ := hn
  have hn0 : ((2*m+1 : ℕ) : ZMod (2*m+1)) = 0 := ZMod.natCast_self _
  push_cast at hn0
  have hk : ((m:ZMod (2*m+1)) + 1) * 2 = 1 := by linear_combination hn0
  constructor
  · intro hx
    cases x with
    | r i =>
      have := hx (DihedralGroup.sr 0) (Subgroup.mem_top _)
      simp at this
      have h2i : i + i = 0 := by linear_combination this
      have hi : i = 0 := by linear_combination (-i) * hk + ((m:ZMod (2*m+1)) + 1) * h2i
      rw [hi]; rfl
    | sr i =>
      have := hx (DihedralGroup.r 1) (Subgroup.mem_top _)
      simp at this
      have h2 : ((2 : ℕ) : ZMod (2*m+1)) = 0 := by
        push_cast
        linear_combination -this
      rw [ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      exfalso; omega
  · rintro rfl
    intro g _
    simp
