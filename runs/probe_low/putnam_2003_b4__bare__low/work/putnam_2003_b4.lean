import Mathlib

open MvPolynomial Set Nat

/--
Let $f(z)=az^4+bz^3+cz^2+dz+e=a(z-r_1)(z-r_2)(z-r_3)(z-r_4)$ where $a,b,c,d,e$ are integers, $a \neq 0$. Show that if $r_1+r_2$ is a rational number and $r_1+r_2 \neq r_3+r_4$, then $r_1r_2$ is a rational number.
-/
theorem putnam_2003_b4
  (f : ℝ → ℝ)
  (a b c d e : ℤ)
  (r1 r2 r3 r4 : ℝ)
  (ane0 : a ≠ 0)
  (hf1 : ∀ z, f z = a * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z + e)
  (hf2 : ∀ z, f z = a * (z - r1) * (z - r2) * (z - r3) * (z - r4)) :
  (¬Irrational (r1 + r2) ∧ r1 + r2 ≠ r3 + r4) → ¬Irrational (r1 * r2) := by
  rintro ⟨hs, hne⟩
  rw [Irrational, not_not] at hs ⊢
  obtain ⟨p, hp⟩ := hs
  have ha : (a:ℝ) ≠ 0 := by exact_mod_cast ane0
  have h : ∀ z:ℝ, (a:ℝ) * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z + e = a * (z - r1) * (z - r2) * (z - r3) * (z - r4) := fun z => by rw [← hf1, hf2]
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have h3 := h 2
  have h4 := h (-2)
  have hb : (b:ℝ) = -a*(r1+r2+r3+r4) := by
    have : (b:ℝ) + a*(r1+r2+r3+r4) = 0 := by
      linear_combination (1/12:ℝ) * ((h3 - h4) - 2*(h1 - h2))
    linarith
  have hd : (d:ℝ) = -a*(r1*r2*(r3+r4)+r3*r4*(r1+r2)) := by
    have : (d:ℝ) + a*(r1*r2*(r3+r4)+r3*r4*(r1+r2)) = 0 := by
      linear_combination (1/12:ℝ) * (-(h3 - h4) + 8*(h1 - h2))
    linarith
  have hc : (c:ℝ) = a*(r1*r2+r3*r4+(r1+r2)*(r3+r4)) := by
    have : (c:ℝ) - a*(r1*r2+r3*r4+(r1+r2)*(r3+r4)) = 0 := by
      linear_combination (1/2:ℝ) * (h1 + h2) - h0
    linarith
  have hq : r1 * r2 * ((r3+r4) - (r1+r2)) = (-(d:ℝ)/a) - (r1+r2)*((c:ℝ)/a - (r1+r2)*(r3+r4)) := by
    rw [hd, hc]
    field_simp
    ring
  have hts : (r3+r4) - (r1+r2) ≠ 0 := fun hh => hne (by linarith)
  have ht : (r3+r4) = -(b:ℝ)/a - (r1+r2) := by
    rw [hb]; field_simp; ring
  refine ⟨(( -(d:ℚ)/a) - p*((c:ℚ)/a - p*(-(b:ℚ)/a - p))) / ((-(b:ℚ)/a - p) - p), ?_⟩
  push_cast
  rw [hp, ← ht, div_eq_iff hts]
  linarith
