import Mathlib

/--
If \( n \) is odd and \( n \geq 3 \), show that the identity is the only element of
\( D_{2n} \) which commutes with all elements of \( D_{2n} \).
-/
theorem DihedralGroup.centralizer_eq_bot {n : ℕ} (hn : Odd n) (h : n ≥ 3) :
    Subgroup.centralizer ⊤ = (⊥ : Subgroup (DihedralGroup n)) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_bot]
  have h2 : ∀ a : ZMod n, a + a = 0 → a = 0 := by
    intro a ha
    have : (2:ZMod n) * a = 0 := by rw [two_mul]; exact ha
    have hu : IsUnit (2 : ZMod n) := by
      have : Nat.Coprime 2 n := (Nat.coprime_two_left).2 hn
      exact_mod_cast (ZMod.unitOfCoprime 2 this).isUnit
    exact hu.mul_right_eq_zero.1 this
  constructor
  · intro hx
    cases x with
    | r i =>
      have := hx (DihedralGroup.sr 0) (Set.mem_univ _)
      simp at this
      rw [DihedralGroup.one_def]
      congr 1
      apply h2
      linear_combination this
    | sr i =>
      exfalso
      have := hx (DihedralGroup.r 1) (Set.mem_univ _)
      simp at this
      have h3 : ((2:ℕ) : ZMod n) = 0 := by
        push_cast; linear_combination -this
      rw [ZMod.natCast_eq_zero_iff] at h3
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  · intro hx
    subst hx
    intro g _
    simp
