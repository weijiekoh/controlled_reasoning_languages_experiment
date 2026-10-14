import Mathlib

open Nat Set Topology Filter

/--
A palindrome in base $b$ is a positive integer whose base-$b$
digits read the same backwards and forwards; for example,
$2002$ is a 4-digit palindrome in base 10. Note that 200 is not
a palindrome in base 10, but it is the 3-digit palindrome
242 in base 9, and 404 in base 7. Prove that there is an integer
which is a 3-digit palindrome in base $b$ for at least 2002
different values of $b$.
-/
theorem putnam_2002_b5
: ∃ n : ℕ, {b : ℕ | b ≥ 1 ∧ (Nat.digits b n).length = 3 ∧ List.Palindrome (Nat.digits b n)}.ncard ≥ 2002 :=
by
  set M : ℕ := Nat.factorial 2002 * 20000000000 with hM
  have hM2 : 20000000000 ≤ M := by
    rw [hM]; exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  have key : ∀ a b c : ℕ, 1 ≤ a → a < b → c < b → 2 ≤ b →
      Nat.digits b (a + b * (c + b * a)) = [a, c, a] := by
    intro a b c ha hab hcb hb
    rw [Nat.digits_add b (by omega) a _ hab (Or.inl (by omega))]
    rw [Nat.digits_add b (by omega) c a hcb (Or.inr (by omega))]
    rw [Nat.digits_of_lt b a (by omega) hab]
  have hdvd : ∀ j : ℕ, 1 ≤ j → j ≤ 2002 → j * (M / j) = M := by
    intro j h1 h2
    have : j ∣ M := Dvd.dvd.mul_right (Nat.dvd_factorial (by omega) h2) _
    exact Nat.mul_div_cancel' this
  have hbound : ∀ j : ℕ, 1 ≤ j → j ≤ 2002 → 2 * j ^ 2 + 2 < M / j := by
    intro j h1 h2
    by_contra hc
    push_neg at hc
    have hj2 : j ^ 2 ≤ 2002 ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : j * (M / j) ≤ 2002 * (2 * 2002 ^ 2 + 2) :=
      Nat.mul_le_mul h2 (by omega)
    rw [hdvd j h1 h2] at h4
    norm_num at h4 <;> omega
  refine ⟨M ^ 2, ?_⟩
  let f : ℕ → ℕ := fun j => M / j - 1
  have hS : ((Finset.Icc 1 2002).image f : Set ℕ) ⊆
      {b : ℕ | b ≥ 1 ∧ (Nat.digits b (M ^ 2)).length = 3 ∧ List.Palindrome (Nat.digits b (M ^ 2))} := by
    intro b hb
    simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc] at hb
    obtain ⟨j, ⟨h1, h2⟩, rfl⟩ := hb
    have hj := hbound j h1 h2
    obtain ⟨b, hb⟩ : ∃ b, M / j = b + 1 := ⟨M / j - 1, by omega⟩
    have hfb : f j = b := by simp only [f, hb]; omega
    rw [hfb]
    have hMe : M = j * (b + 1) := by rw [← hb, hdvd j h1 h2]
    have hn : M ^ 2 = j ^ 2 + b * (2 * j ^ 2 + b * j ^ 2) := by
      rw [hMe]; ring
    have hdig : Nat.digits b (M ^ 2) = [j ^ 2, 2 * j ^ 2, j ^ 2] := by
      rw [hn]
      exact key (j ^ 2) b (2 * j ^ 2) (Nat.one_le_pow _ _ (by omega)) (by omega) (by omega) (by omega)
    refine ⟨by omega, ?_, ?_⟩
    · rw [hdig]; rfl
    · rw [hdig]
      apply List.Palindrome.of_reverse_eq
      simp
  have hinj : Set.InjOn f (Finset.Icc 1 2002 : Set ℕ) := by
    intro j hj k hk hjk
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj hk
    have hj' := hbound j hj.1 hj.2
    have hk' := hbound k hk.1 hk.2
    have heq : M / j = M / k := by
      simp only [f] at hjk; omega
    have hpos : 0 < M / j := by omega
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hdvd j hj.1 hj.2, heq, hdvd k hk.1 hk.2]
  have hfin : {b : ℕ | b ≥ 1 ∧ (Nat.digits b (M ^ 2)).length = 3 ∧
      List.Palindrome (Nat.digits b (M ^ 2))}.Finite := by
    refine (Set.finite_Iic (M ^ 2)).subset ?_
    rintro b ⟨hb1, hlen, _⟩
    simp only [Set.mem_Iic]
    by_contra hc
    push_neg at hc
    rw [Nat.digits_of_lt b _ (pow_ne_zero _ (by omega)) hc] at hlen
    simp at hlen
  have := Set.ncard_le_ncard hS hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at this
  simp only [Nat.card_Icc] at this
  omega
