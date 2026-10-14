import Mathlib

open Filter Topology Set Nat

/--
Let $p$ be a prime number. Let $h(x)$ be a polynomial with integer coefficients such that $h(0), h(1), \dots, h(p^2-1)$ are distinct modulo $p^2$. Show that $h(0), h(1), \dots, h(p^3-1)$ are distinct modulo $p^3$.
-/
theorem putnam_2008_b4
(p : ℕ)
(hp : Nat.Prime p)
(h : Polynomial ℤ)
(hh : ∀ i j : Finset.range (p ^ 2), h.eval i ≡ h.eval j [ZMOD p ^ 2] → i = j)
: (∀ i j : Finset.range (p ^ 3), h.eval i ≡ h.eval j [ZMOD p ^ 3] → i = j) :=
by
  have hp2 : 2 ≤ p := hp.two_le
  have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : (0:ℤ) < p := by exact_mod_cast hp.pos
  have hp2Z : (2:ℤ) ≤ p := by exact_mod_cast hp2
  have taylor : ∀ x y : ℤ, ∃ k : ℤ, h.eval (x + y) = h.eval x + h.derivative.eval x * y + k * y^2 := by
    intro x y
    exact ⟨(Polynomial.binomExpansion h x y).1, (Polynomial.binomExpansion h x y).2⟩
  -- Key lemma: p does not divide h'(a) for any integer a.
  have hD : ∀ a : ℤ, ¬ (p:ℤ) ∣ h.derivative.eval a := by
    intro a ha
    obtain ⟨r, hr⟩ : ∃ r, r = a % (p:ℤ) := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg a (ne_of_gt hpos)
    have hrp : r < p := by rw [hr]; exact Int.emod_lt_of_pos a hpos
    have har : (p:ℤ) ∣ a - r := ⟨a / p, by rw [hr]; linarith [Int.emod_def a p]⟩
    have hDr : (p:ℤ) ∣ h.derivative.eval r := by
      have h1 : (p:ℤ) ∣ h.derivative.eval a - h.derivative.eval r :=
        dvd_trans har (Polynomial.sub_dvd_eval_sub a r _)
      have h2 := dvd_sub ha h1
      simpa using h2
    obtain ⟨c, hc⟩ := hDr
    obtain ⟨k, hk⟩ := taylor r p
    have key : h.eval r ≡ h.eval (r + p) [ZMOD (p:ℤ)^2] :=
      Int.modEq_iff_dvd.mpr ⟨c + k, by rw [hk, hc]; ring⟩
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i:ℤ) = r := ⟨r.toNat, Int.toNat_of_nonneg hr0⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j:ℤ) = r + p := ⟨(r+p).toNat, Int.toNat_of_nonneg (by linarith)⟩
    have hi2 : i < p^2 := by
      have : (i:ℤ) < (p:ℤ)^2 := by rw [hi]; nlinarith
      exact_mod_cast this
    have hj2 : j < p^2 := by
      have : (j:ℤ) < (p:ℤ)^2 := by rw [hj]; nlinarith
      exact_mod_cast this
    have hij : i = j := congrArg Subtype.val (hh ⟨i, Finset.mem_range.mpr hi2⟩ ⟨j, Finset.mem_range.mpr hj2⟩ (by
      show h.eval (i:ℤ) ≡ h.eval (j:ℤ) [ZMOD (p:ℤ)^2]
      rw [hi, hj]; exact key))
    have : (i:ℤ) = j := by rw [hij]
    rw [hi, hj] at this
    linarith
  -- Reduction modulo p^2.
  have red : ∀ x : ℤ, h.eval (x % (p:ℤ)^2) ≡ h.eval x [ZMOD (p:ℤ)^2] := by
    intro x
    have hdiv : (p:ℤ)^2 ∣ x - x % (p:ℤ)^2 := ⟨x / (p:ℤ)^2, by linarith [Int.emod_def x ((p:ℤ)^2)]⟩
    exact Int.modEq_iff_dvd.mpr (dvd_trans hdiv (Polynomial.sub_dvd_eval_sub _ _ _))
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  by_contra hne
  have hi' : i < p^3 := Finset.mem_range.mp hi
  have hj' : j < p^3 := Finset.mem_range.mp hj
  have hmod3 : h.eval (i:ℤ) ≡ h.eval (j:ℤ) [ZMOD (p:ℤ)^3] := hij
  have h2 : h.eval (i:ℤ) ≡ h.eval (j:ℤ) [ZMOD (p:ℤ)^2] :=
    Int.ModEq.of_dvd (pow_dvd_pow _ (by norm_num)) hmod3
  have hcast : ∀ n : ℕ, ((n % p^2 : ℕ) : ℤ) = (n:ℤ) % (p:ℤ)^2 := by
    intro n; simp
  have hred : h.eval (((i % p^2 : ℕ)):ℤ) ≡ h.eval (((j % p^2 : ℕ)):ℤ) [ZMOD (p:ℤ)^2] := by
    rw [hcast i, hcast j]; exact (red _).trans (h2.trans (red _).symm)
  have hsame : i % p^2 = j % p^2 :=
    congrArg Subtype.val (hh ⟨i % p^2, Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))⟩
      ⟨j % p^2, Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))⟩ hred)
  have hmodZ : (i:ℤ) ≡ (j:ℤ) [ZMOD (p:ℤ)^2] := by
    unfold Int.ModEq; rw [← hcast i, ← hcast j, hsame]
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp hmodZ)
  obtain ⟨k, hk⟩ := taylor (i:ℤ) ((j:ℤ) - i)
  rw [show (i:ℤ) + ((j:ℤ) - i) = j by ring, ht] at hk
  have h3 : (p:ℤ)^3 ∣ h.eval (j:ℤ) - h.eval (i:ℤ) := hmod3.dvd
  have h4 : (p:ℤ)^2 * (h.derivative.eval (i:ℤ) * t)
      = (h.eval (j:ℤ) - h.eval (i:ℤ)) - (p:ℤ)^3 * (p * k * t^2) := by
    linear_combination (-1:ℤ) * hk
  have h5 : (p:ℤ)^2 * (p:ℤ) ∣ (p:ℤ)^2 * (h.derivative.eval (i:ℤ) * t) := by
    have e : (p:ℤ)^2 * p = (p:ℤ)^3 := by ring
    rw [e, h4]
    exact dvd_sub h3 (dvd_mul_right _ _)
  have h6 : (p:ℤ) ∣ h.derivative.eval (i:ℤ) * t :=
    (mul_dvd_mul_iff_left (pow_ne_zero 2 hpZ.ne_zero)).mp h5
  rcases hpZ.dvd_or_dvd h6 with hd | hd
  · exact hD _ hd
  · obtain ⟨s, hs⟩ := hd
    have hdvd : (p:ℤ)^3 ∣ (j:ℤ) - i := ⟨s, by rw [ht, hs]; ring⟩
    have hlt : |(j:ℤ) - i| < (p:ℤ)^3 := by
      have hiZ : (i:ℤ) < p^3 := by exact_mod_cast hi'
      have hjZ : (j:ℤ) < p^3 := by exact_mod_cast hj'
      have hi0 : (0:ℤ) ≤ i := Nat.cast_nonneg i
      have hj0 : (0:ℤ) ≤ j := Nat.cast_nonneg j
      rw [abs_lt]; constructor <;> linarith
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    apply hne
    apply Subtype.ext
    show i = j
    omega
