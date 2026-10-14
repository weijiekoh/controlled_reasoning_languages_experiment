import Mathlib

/--
If \( n \) is odd and \( n \geq 3 \), show that the identity is the only element of
\( D_{2n} \) which commutes with all elements of \( D_{2n} \).
-/
theorem DihedralGroup.centralizer_eq_bot {n : ℕ} (hn : Odd n) (h : n ≥ 3) :
    Subgroup.centralizer ⊤ = (⊥ : Subgroup (DihedralGroup n)) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := hn
  have hn0 : ((2*k+1 : ℕ) : ZMod (2*k+1)) = 0 := ZMod.natCast_self _
  push_cast at hn0
  constructor
  · intro hc
    cases x with
    | r i =>
      have h1 := hc (DihedralGroup.sr 0) trivial
      simp at h1
      have h2 : i = 0 := by
        linear_combination i * hn0 - (k : ZMod (2*k+1)) * h1
      subst h2
      rfl
    | sr i =>
      have h1 := hc (DihedralGroup.r 1) trivial
      simp at h1
      exfalso
      have h2 : ((2 : ℕ) : ZMod (2*k+1)) = 0 := by
        push_cast
        linear_combination -h1
      have h3 := (CharP.cast_eq_zero_iff (ZMod (2*k+1)) (2*k+1) 2).mp h2
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  · rintro rfl g _
    simp
