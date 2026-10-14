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
  obtain ⟨F, hF⟩ : ∃ F, F = Nat.factorial 2002 := ⟨_, rfl⟩
  have hFpos : 0 < F := by rw [hF]; exact Nat.factorial_pos _
  have hdvd : ∀ e, 1 ≤ e → e ≤ 2002 → e ∣ F := by
    intro e h1 h2; rw [hF]; exact Nat.dvd_factorial (by omega) h2
  have hle : ∀ e, 1 ≤ e → e ≤ 2002 → e ≤ F := by
    intro e h1 h2; exact Nat.le_of_dvd hFpos (hdvd e h1 h2)
  have key : ∀ N e m : ℕ, 1 ≤ e → 2*e^2+2 ≤ m → (e*m)^2 = N →
      m-1 ∈ {b : ℕ | b ≥ 1 ∧ (Nat.digits b N).length = 3 ∧ List.Palindrome (Nat.digits b N)} := by
    intro N e m he hm hN
    obtain ⟨b, rfl⟩ : ∃ b, m = b+1 := ⟨m-1, by omega⟩
    rw [Nat.add_sub_cancel]
    subst hN
    have he1 : 1 ≤ e^2 := Nat.one_le_pow _ _ (by omega)
    have hb1 : e^2 < b := by linarith
    have hb2 : 2*e^2 < b := by linarith
    have hb3 : 1 < b := by linarith
    have he2 : e^2 ≠ 0 := by intro h; linarith
    have he3 : 2*e^2 ≠ 0 := by intro h; linarith
    have hn : (e*(b+1))^2 = e^2 + b*(2*e^2 + b*e^2) := by ring
    have hd : Nat.digits b ((e*(b+1))^2) = [e^2, 2*e^2, e^2] := by
      rw [hn, Nat.digits_add b hb3 _ _ hb1 (Or.inl he2),
        Nat.digits_add b hb3 _ _ hb2 (Or.inl he3), Nat.digits_of_lt b _ he2 hb1]
    refine ⟨(Nat.zero_le _).trans_lt hb3, ?_, ?_⟩
    · rw [hd]; simp
    · rw [hd]; apply List.Palindrome.of_reverse_eq; simp
  have hfinN : ∀ N : ℕ, 0 < N →
      {b : ℕ | b ≥ 1 ∧ (Nat.digits b N).length = 3 ∧ List.Palindrome (Nat.digits b N)}.Finite := by
    intro N hN
    apply (Finset.range (N + 1)).finite_toSet.subset
    rintro b ⟨hb1, hlen, -⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    by_cases hb : b ≤ 1
    · omega
    · rw [not_le] at hb
      have h := Nat.base_pow_length_digits_le b N hb (by omega)
      rw [hlen] at h
      nlinarith [mul_pos (by omega : 0 < b) (by omega : 0 < b)]
  have hNpos : 0 < (F*10^7)^2 := pow_pos (Nat.mul_pos hFpos (by norm_num)) 2
  refine ⟨(F*10^7)^2, ?_⟩
  have hfin := hfinN _ hNpos
  have hsub : ((Finset.Icc 1 2002).image (fun e => F/e*10^7 - 1) : Set ℕ) ⊆
      {b : ℕ | b ≥ 1 ∧ (Nat.digits b ((F*10^7)^2)).length = 3 ∧
        List.Palindrome (Nat.digits b ((F*10^7)^2))} := by
    intro b hb
    simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc] at hb
    obtain ⟨e, ⟨h1, h2⟩, rfl⟩ := hb
    have hk : 1 ≤ F/e := Nat.div_pos (hle e h1 h2) (by omega)
    have hk2 : 1*10^7 ≤ F/e*10^7 := Nat.mul_le_mul_right _ hk
    have he2 : e^2 ≤ 2002^2 := Nat.pow_le_pow_left h2 2
    have hineq : 2*e^2+2 ≤ F/e*10^7 := by nlinarith
    have heq : e*(F/e*10^7) = F*10^7 := by
      rw [← mul_assoc, Nat.mul_div_cancel' (hdvd e h1 h2)]
    exact key _ e (F/e*10^7) h1 hineq (by rw [heq])
  have hinj : Set.InjOn (fun e => F/e*10^7 - 1) (Finset.Icc 1 2002 : Set ℕ) := by
    intro e he e' he' heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at he he'
    have hk : 1 ≤ F/e := Nat.div_pos (hle e he.1 he.2) (by omega)
    have hk' : 1 ≤ F/e' := Nat.div_pos (hle e' he'.1 he'.2) (by omega)
    have h3 : F/e = F/e' := by
      simp only at heq
      generalize F/e = k at *
      generalize F/e' = k' at *
      omega
    have hF1 : e*(F/e) = F := Nat.mul_div_cancel' (hdvd e he.1 he.2)
    have hF2 : e'*(F/e') = F := Nat.mul_div_cancel' (hdvd e' he'.1 he'.2)
    rw [← h3] at hF2
    exact Nat.eq_of_mul_eq_mul_right hk (hF1.trans hF2.symm)
  have hcard : ((Finset.Icc 1 2002).image (fun e => F/e*10^7 - 1)).card = 2002 := by
    rw [Finset.card_image_of_injOn hinj]; simp
  calc 2002 = (((Finset.Icc 1 2002).image (fun e => F/e*10^7 - 1) : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub hfin
