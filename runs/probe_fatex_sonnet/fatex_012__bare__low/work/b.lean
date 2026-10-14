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
  have red : ∀ n S : ℤ, 0 < n → ∃ e : ℤ, -n ≤ S - 2*e*n ∧ S - 2*e*n < n := by
    intro n S hn
    refine ⟨(S+n)/(2*n), ?_⟩
    have h1 := Int.emod_add_mul_ediv (S+n) (2*n)
    have h2 := Int.emod_nonneg (S+n) (show 2*n ≠ 0 by omega)
    have h3 := Int.emod_lt_of_pos (S+n) (show 0 < 2*n by omega)
    generalize (S+n)/(2*n) = e at *
    generalize (S+n)%(2*n) = r at *
    constructor <;> nlinarith
  have L1 : ∀ n P Q f : ℤ, 0 < n → 19*(Q-f*n)^2 < 3*n^2 → ¬ (n ∣ P ∧ n ∣ Q) → G n P Q := by
    intro n P Q f hn hb hnd
    obtain ⟨e, he1, he2⟩ := red n (2*P + (Q - f*n)) hn
    rw [hG]
    refine ⟨e, f, ?_, ?_⟩
    · by_contra h
      push_neg at h
      have hb0 : Q - f*n = 0 := by nlinarith [sq_nonneg (2*(P-e*n)+(Q-f*n)), sq_nonneg (Q-f*n)]
      have ha0 : P - e*n = 0 := by nlinarith
      exact hnd ⟨⟨e, by linarith⟩, ⟨f, by linarith⟩⟩
    · nlinarith [sq_nonneg (2*(P-e*n)+(Q-f*n)), sq_nonneg (Q-f*n)]
  have core : ∀ a b n : ℤ, 0 < n → 0 < b → 2*b ≤ n → -n ≤ 2*a+b → 2*a+b ≤ n → 
      ∃ c d : ℤ, G n (c*a - 5*d*b) (c*b+d*a+d*b) := by
    intro a b n hn hb hb2 ha1 ha2
    by_cases hs : 19*b^2 < 3*n^2
    · refine ⟨1, 0, ?_⟩
      rw [hG]
      refine ⟨0, 0, ?_, ?_⟩
      · nlinarith [sq_nonneg (2*a+b), sq_nonneg b]
      · nlinarith [sq_nonneg (2*a+b), sq_nonneg b]
    · push_neg at hs
      by_cases hd : n ∣ 2*a ∧ n ∣ 2*b
      · obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := hd
        have hk1 : k = 1 := by
          have : 0 < k := by by_contra h; push_neg at h; nlinarith
          have : k ≤ 1 := by by_contra h; push_neg at h; nlinarith
          omega
        subst hk1
        have hj1 : -1 ≤ j := by by_contra h; push_neg at h; nlinarith
        have hj2 : j ≤ 0 := by by_contra h; push_neg at h; nlinarith
        have : j = 0 ∨ j = -1 := by omega
        rcases this with rfl | rfl
        · refine ⟨1, 1, ?_⟩
          rw [hG]
          refine ⟨-2, 1, ?_, ?_⟩ <;> nlinarith
        · refine ⟨0, 1, ?_⟩
          rw [hG]
          refine ⟨-2, 0, ?_, ?_⟩ <;> nlinarith
      · refine ⟨2, 0, ?_⟩
        have := L1 n (2*a) (2*b) 1 hn ?_ hd
        · simpa using this
        · nlinarith
  intro A B n hn h
  obtain ⟨f, hf1, hf2⟩ := red n (2*B) hn
  obtain ⟨b, hb⟩ : ∃ b, b = B - f*n := ⟨_, rfl⟩
  obtain ⟨e, he1, he2⟩ := red n (2*A+b) hn
  obtain ⟨a, ha⟩ : ∃ a, a = A - e*n := ⟨_, rfl⟩
  have hA : A = a + e*n := by linarith
  have hB : B = b + f*n := by linarith
  subst hA hB
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    exact h ⟨⟨e, by ring⟩, ⟨f, by ring⟩⟩
  have key : ∃ c d : ℤ, G n (c*a - 5*d*b) (c*b+d*a+d*b) := by
    rcases lt_trichotomy b 0 with hneg | hzero | hpos
    · obtain ⟨c, d, hcd⟩ := core (-a) (-b) n hn (by linarith) (by linarith) (by linarith) (by linarith)
      refine ⟨c, d, ?_⟩
      have := neg _ _ _ hcd
      convert this using 2 <;> ring
    · subst hzero
      have ha0 : a ≠ 0 := fun h0 => hab ⟨h0, rfl⟩
      refine ⟨1, 0, ?_⟩
      rw [hG]
      refine ⟨0, 0, ?_, ?_⟩
      · have := sq_pos_of_ne_zero ha0
        nlinarith
      · nlinarith
    · exact core a b n hn hpos (by linarith) (by linarith) (by linarith)
  obtain ⟨c, d, hcd⟩ := key
  have := shift n _ _ (c*e - 5*d*f) (c*f + d*e + d*f) hcd
  rw [hG] at this
  obtain ⟨e', f', h1, h2⟩ := this
  refine ⟨c, d, e', f', ?_, ?_⟩
  · convert h1 using 3 <;> ring
  · convert h2 using 3 <;> ring
