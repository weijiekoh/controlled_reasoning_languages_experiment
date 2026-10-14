import Mathlib

theorem intpart : ∀ (A B n : ℤ), 0 < n → ¬ (n ∣ A ∧ n ∣ B) → ∃ c d e f : ℤ,
    0 < (c*A - 5*d*B - e*n)^2 + (c*A - 5*d*B - e*n)*(c*B+d*A+d*B - f*n) + 5*(c*B+d*A+d*B - f*n)^2 ∧
    (c*A - 5*d*B - e*n)^2 + (c*A - 5*d*B - e*n)*(c*B+d*A+d*B - f*n) + 5*(c*B+d*A+d*B - f*n)^2 < n^2 := by
  obtain ⟨G, hG⟩ : ∃ G : ℤ → ℤ → ℤ → Prop, ∀ n P Q, G n P Q ↔ ∃ e f : ℤ,
      0 < (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 ∧ (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 < n^2 :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  have shift : ∀ n P Q k l, G n P Q → G n (P + k*n) (Q + l*n) := by
    intro n P Q k l h
    rw [hG] at h ⊢
    obtain ⟨e, f, h1⟩ := h
    refine ⟨e + k, f + l, ?_⟩
    have e1 : P + k*n - (e+k)*n = P - e*n := by ring
    have e2 : Q + l*n - (f+l)*n = Q - f*n := by ring
    rw [e1, e2]; exact h1
  have neg : ∀ n P Q, G n P Q → G n (-P) (-Q) := by
    intro n P Q h
    rw [hG] at h ⊢
    obtain ⟨e, f, h1, h2⟩ := h
    refine ⟨-e, -f, ?_, ?_⟩
    · have : (-P - -e*n)^2+(-P - -e*n)*(-Q - -f*n)+5*(-Q - -f*n)^2 = (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 := by ring
      rw [this]; exact h1
    · have : (-P - -e*n)^2+(-P - -e*n)*(-Q - -f*n)+5*(-Q - -f*n)^2 = (P-e*n)^2+(P-e*n)*(Q-f*n)+5*(Q-f*n)^2 := by ring
      rw [this]; exact h2
  -- reduction
  have red : ∀ n P : ℤ, 0 < n → ∃ e : ℤ, -n ≤ 2*(P - e*n) ∧ 2*(P-e*n) < n := by
    intro n P hn
    refine ⟨(2*P+n)/(2*n), ?_⟩
    have h1 := Int.ediv_add_emod (2*P+n) (2*n)
    have h2 := Int.emod_nonneg (2*P+n) (show 2*n ≠ 0 by omega)
    have h3 := Int.emod_lt_of_pos (2*P+n) (show 0 < 2*n by omega)
    generalize (2*P+n)/(2*n) = e at *
    generalize (2*P+n)%(2*n) = r at *
    constructor <;> nlinarith
  have L1 : ∀ n P Q f : ℤ, 0 < n → 19*(Q-f*n)^2 < 3*n^2 → ¬ (n ∣ P ∧ n ∣ Q) → G n P Q := by
    intro n P Q f hn hb hnd
    obtain ⟨e, he1, he2⟩ := red n (2*P + (Q - f*n)) hn
    rw [hG]
    refine ⟨?_, f, ?_⟩
    sorry
  sorry
