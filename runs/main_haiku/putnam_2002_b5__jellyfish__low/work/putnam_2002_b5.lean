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
: ∃ n : ℕ, {b : ℕ | b ≥ 1 ∧ (Nat.digits b n).length = 3 ∧ List.Palindrome (Nat.digits b n)}.ncard ≥ 2002 := by
  have key : ∀ b a : ℕ, 1 ≤ a → a < b → 2*a < b →
      Nat.digits b (a + b*(2*a + b*a)) = [a, 2*a, a] := by
    intro b a ha hab h2
    rw [Nat.digits_add b (by omega) a _ (by omega) (Or.inl (by omega)),
      Nat.digits_add b (by omega) (2*a) a (by omega) (Or.inl (by omega)),
      Nat.digits_of_lt b a (by omega) hab]
  have hid : ∀ b a : ℕ, a*(b+1)^2 = a + b*(2*a+b*a) := by
    intro b a; ring
  have h4 : ∀ i : ℕ, (4:ℕ)^i = 2^(2*i) := by
    intro i; rw [pow_mul]; norm_num
  have hn : ∀ i ≤ 6008, (2:ℕ)^(2*6008) = 4^i * (2^(6008-i))^2 := by
    intro i hi
    rw [h4, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hmem : ∀ i < 2002, (2^(6008-i) - 1) ∈
      {b : ℕ | b ≥ 1 ∧ (Nat.digits b (2^(2*6008))).length = 3 ∧
        List.Palindrome (Nat.digits b (2^(2*6008)))} := by
    intro i hi
    have hd1 : 1 ≤ 2^(6008-i) := Nat.one_le_two_pow
    have hp1 : 1 ≤ (4:ℕ)^i := Nat.one_le_pow _ _ (by norm_num)
    have hlt2 : 2^(2*i+2) < 2^(6008-i) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hA : (2:ℕ)^(2*i+2) = 4*4^i := by rw [h4, pow_add]; ring
    have h1 : 4^i < 2^(6008-i) - 1 := by omega
    have h2 : 2*4^i < 2^(6008-i) - 1 := by omega
    have hb : (2^(6008-i) - 1) + 1 = 2^(6008-i) := by omega
    have hnb : (2:ℕ)^(2*6008) = 4^i * ((2^(6008-i) - 1) + 1)^2 := by
      rw [hb]; exact hn i (by omega)
    show _ ≥ 1 ∧ _
    refine ⟨by omega, ?_⟩
    rw [hnb, hid, key _ _ hp1 h1 h2]
    exact ⟨by simp, List.Palindrome.of_reverse_eq (by simp)⟩
  refine ⟨2^(2*6008), ?_⟩
  set S := {b : ℕ | b ≥ 1 ∧ (Nat.digits b (2^(2*6008))).length = 3 ∧
        List.Palindrome (Nat.digits b (2^(2*6008)))} with hS
  have hfin : S.Finite := by
    apply (Set.finite_Iic (2^(2*6008))).subset
    intro b hb
    obtain ⟨_, hlen, _⟩ := hb
    show b ≤ 2^(2*6008)
    by_contra h
    push_neg at h
    have hne : (2:ℕ)^(2*6008) ≠ 0 := by positivity
    rw [Nat.digits_of_lt b _ hne h] at hlen
    simp at hlen
  have hinj : Set.InjOn (fun i => 2^(6008-i) - 1) (Finset.range 2002 : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h1 : 1 ≤ 2^(6008-i) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2^(6008-j) := Nat.one_le_two_pow
    have h3 : 2^(6008-i) = 2^(6008-j) := by have : 2^(6008-i) - 1 = 2^(6008-j) - 1 := hij; omega
    have h5 := Nat.pow_right_injective (le_refl 2) h3
    omega
  have hsub : ((Finset.range 2002).image (fun i => 2^(6008-i) - 1) : Set ℕ) ⊆ S := by
    intro b hb
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hmem i hi
  have hcard : ((Finset.range 2002).image (fun i => 2^(6008-i) - 1) : Set ℕ).ncard = 2002 := by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact hinj (by simpa using hi) (by simpa using hj) hij
  have := Set.ncard_le_ncard hsub hfin
  omega
