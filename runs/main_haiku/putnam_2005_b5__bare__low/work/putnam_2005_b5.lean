import Mathlib

open Nat Set
open MvPolynomial

variable {n : ℕ}

lemma comp_monomial (d : ℕ) (u : Fin n →₀ ℕ) (a : ℝ) :
    homogeneousComponent d (monomial u a) = if Finsupp.degree u = d then monomial u a else 0 := by
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial a rfl)]
  by_cases h : d = Finsupp.degree u
  · simp [h]
  · simp [h, Ne.symm h]

lemma deg_sub_single (u : Fin n →₀ ℕ) (i : Fin n) (h : 1 ≤ u i) :
    Finsupp.degree (u - Finsupp.single i 1) + 1 = Finsupp.degree u := by
  have hle : Finsupp.single i 1 ≤ u := by
    rw [Finsupp.single_le_iff]; exact h
  have h1 : u = (u - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  have h2 := congrArg Finsupp.degree h1
  rw [map_add, Finsupp.degree_single] at h2
  omega

lemma comp_pderiv (i : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) ℝ) :
    homogeneousComponent d (pderiv i f) = pderiv i (homogeneousComponent (d+1) f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [pderiv_monomial, comp_monomial, comp_monomial]
    by_cases hu : u i = 0
    · split_ifs <;> simp_all [pderiv_monomial]
    · have h1 : 1 ≤ u i := Nat.one_le_iff_ne_zero.mpr hu
      have key := deg_sub_single u i h1
      by_cases hd : Finsupp.degree u = d + 1
      · have hd' : Finsupp.degree (u - Finsupp.single i 1) = d := by omega
        simp [hd, hd']
      · have hd' : Finsupp.degree (u - Finsupp.single i 1) ≠ d := by omega
        simp [hd, hd']
  | add p q hp hq =>
    simp only [map_add, hp, hq]

lemma comp_mul_hom (g : MvPolynomial (Fin n) ℝ) (k : ℕ) (hg : g.IsHomogeneous k)
    (f : MvPolynomial (Fin n) ℝ) (e : ℕ) :
    homogeneousComponent e (g * f) = if k ≤ e then g * homogeneousComponent (e - k) f else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent f, Finset.mul_sum, map_sum]
  have hterm : ∀ m ∈ Finset.range (f.totalDegree + 1),
      homogeneousComponent e (g * homogeneousComponent m f)
        = if e = k + m then g * homogeneousComponent m f else 0 := by
    intro m _
    rw [homogeneousComponent_of_mem]
    rw [mem_homogeneousSubmodule]
    exact hg.mul (homogeneousComponent_isHomogeneous m f)
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hk
  · rw [Finset.sum_eq_single (e - k)]
    · rw [if_pos (by omega)]
    · intro m _ hm
      rw [if_neg (by omega)]
    · intro h
      have h0 : homogeneousComponent (e - k) f = 0 :=
        homogeneousComponent_eq_zero _ _ (by simp at h; omega)
      rw [if_pos (by omega), h0, mul_zero]
  · apply Finset.sum_eq_zero
    intro m _
    rw [if_neg (by omega)]

lemma r2_hom : (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro j _
  have := (isHomogeneous_X ℝ j).pow 2
  simpa using this

lemma r2_ne_zero (hn : 0 < n) : (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ => (1:ℝ))) h
  simp [map_sum] at this
  have : (0:ℝ) < n := by exact_mod_cast hn
  linarith [this]


lemma pderiv_r2' (i : Fin n) :
    pderiv i (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) = 2 * X i := by
  simp [map_sum, pderiv_X, Pi.single_apply]

lemma pderiv_two (i : Fin n) : pderiv i (2 : MvPolynomial (Fin n) ℝ) = 0 := by
  rw [show (2 : MvPolynomial (Fin n) ℝ) = C 2 from rfl, pderiv_C]

lemma lap_r2 (R : MvPolynomial (Fin n) ℝ) (f : ℕ) (hR : R.IsHomogeneous f) :
    ∑ i, pderiv i (pderiv i ((∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * R))
      = C (2 * (n:ℝ) + 4 * (f:ℝ)) * R
        + (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * ∑ i, pderiv i (pderiv i R) := by
  have hi : ∀ i : Fin n, pderiv i (pderiv i ((∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * R))
      = 2 * R + 4 * (X i * pderiv i R)
        + (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * pderiv i (pderiv i R) := by
    intro i
    simp only [map_add, pderiv_mul, pderiv_r2', pderiv_two, pderiv_X]
    simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  have hE := hR.sum_X_mul_pderiv
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, hE, nsmul_eq_mul, map_add, map_mul, map_natCast, map_ofNat]
  ring

lemma key_L (hn : 0 < n) : ∀ e : ℕ, ∀ c : ℝ, 0 < c → ∀ H : MvPolynomial (Fin n) ℝ,
    H.IsHomogeneous e →
    C c * H + (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * ∑ i, pderiv i (pderiv i H) = 0 →
    H = 0 := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro c hc H hH heq
  have hcc : C c⁻¹ * C c = (1 : MvPolynomial (Fin n) ℝ) := by
    rw [← C_mul, inv_mul_cancel₀ hc.ne', C_1]
  obtain ⟨R0, hdiv⟩ : ∃ R0 : MvPolynomial (Fin n) ℝ,
      H = (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * R0 := by
    refine ⟨-(C c⁻¹ * ∑ i, pderiv i (pderiv i H)), ?_⟩
    linear_combination (C c⁻¹) * heq - H * hcc
  have hH' : homogeneousComponent e H = H := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hH)]
    simp
  have h1 : homogeneousComponent e
      ((∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * R0)
        = if 2 ≤ e then (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2)
            * homogeneousComponent (e - 2) R0 else 0 :=
    comp_mul_hom _ 2 r2_hom R0 e
  rw [← hdiv, hH'] at h1
  by_cases he : e < 2
  · rw [if_neg (by omega)] at h1
    rw [h1]
  · have he := not_lt.mp he
    rw [if_pos he] at h1
    set R := homogeneousComponent (e - 2) R0 with hRdef
    have hR : R.IsHomogeneous (e - 2) := homogeneousComponent_isHomogeneous _ _
    subst h1
    have hL := lap_r2 R (e - 2) hR
    have heq2 : (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) *
        (C (c + (2 * (n:ℝ) + 4 * ((e - 2 : ℕ) : ℝ))) * R
          + (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * ∑ i, pderiv i (pderiv i R)) = 0 := by
      rw [map_add]
      linear_combination heq - (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * hL
    have heq3 := (mul_eq_zero.mp heq2).resolve_left (r2_ne_zero hn)
    have hpos : (0:ℝ) < c + (2 * (n:ℝ) + 4 * ((e - 2 : ℕ) : ℝ)) := by
      have : (0:ℝ) ≤ 2 * (n:ℝ) + 4 * ((e - 2 : ℕ) : ℝ) := by positivity
      linarith
    have hR0 := ih (e - 2) (by omega) _ hpos R hR heq3
    rw [hR0, mul_zero]

lemma comp_lap (P : MvPolynomial (Fin n) ℝ) (d : ℕ) :
    homogeneousComponent d (∑ i, pderiv i (pderiv i P))
      = ∑ i, pderiv i (pderiv i (homogeneousComponent (d+2) P)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [comp_pderiv, comp_pderiv]


/--
Let $P(x_1,\dots,x_n)$ denote a polynomial with real coefficients in the variables $x_1, \dots, x_n$, and suppose that
\[
\left( \frac{\partial^2}{\partial x_1^2} + \cdots + \frac{\partial^2}{\partial x_n^2}\right) P(x_1, \dots,x_n) = 0 \quad \mbox{(identically)}
\]
and that
\[
x_1^2 + \cdots + x_n^2 \mbox{ divides } P(x_1, \dots, x_n).
\]
Show that $P=0$ identically.
-/
theorem putnam_2005_b5
(n : ℕ)
(npos : n > 0)
(P : MvPolynomial (Fin n) ℝ)
(hderiv : ∑ i : Fin n, (MvPolynomial.pderiv i)^[2] P = 0)
(hsumsq : ∑ i : Fin n, (MvPolynomial.X i) ^ 2 ∣ P)
: (P = 0) := by
  obtain ⟨Q, hQ⟩ := hsumsq
  have hΔ : ∑ i, pderiv i (pderiv i P) = 0 := by
    have : ∀ i : Fin n, (pderiv i)^[2] P = pderiv i (pderiv i P) := fun i => rfl
    simpa only [this] using hderiv
  have hcomp : ∀ d, homogeneousComponent d Q = 0 := by
    intro d
    have h1 := comp_lap P d
    rw [hΔ, map_zero] at h1
    have hP2 : homogeneousComponent (d+2) P
        = (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) * homogeneousComponent d Q := by
      rw [hQ, comp_mul_hom _ 2 r2_hom, if_pos (by omega), show d + 2 - 2 = d from by omega]
    rw [hP2, lap_r2 _ d (homogeneousComponent_isHomogeneous _ _)] at h1
    have hnpos : (0:ℝ) < n := by exact_mod_cast npos
    have hd : (0:ℝ) ≤ 4 * (d:ℝ) := by positivity
    have := key_L npos d (2 * (n:ℝ) + 4 * (d:ℝ)) (by linarith) _
      (homogeneousComponent_isHomogeneous d Q) h1.symm
    exact this
  have hQ0 : Q = 0 := by
    rw [← sum_homogeneousComponent Q]
    exact Finset.sum_eq_zero (fun d _ => hcomp d)
  rw [hQ, hQ0, mul_zero]
