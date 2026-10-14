import Mathlib
theorem L3 {R : Type} [CommRing R] [IsDomain R] (m p : Ideal R) [m.IsPrime] [p.IsPrime]
    (h0 : p ≠ ⊥) (h1 : p < m) : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  have hp : ¬ p.height ≤ (0:ℕ) := by
    rw [Ideal.height_le_iff]
    intro h
    have := h ⊥ Ideal.isPrime_bot (bot_lt_iff_ne_bot.2 h0)
    simp at this
  have hm : ¬ m.height ≤ (1:ℕ) := by
    rw [Ideal.height_le_iff]
    intro h
    have := h p inferInstance h1
    apply hp
    have : p.height < 1 := by simpa using this
    exact Order.lt_one_iff_nonpos.1 this |>.trans (le_refl _) 
  have : (2:ℕ∞) ≤ m.height := by
    by_contra hc
    rw [not_le] at hc
    apply hm
    generalize m.height = h at hc ⊢
    induction h using ENat.recTopCoe with
    | top => simp at hc
    | coe n =>
      have : n < 2 := by exact_mod_cast hc
      exact_mod_cast (by omega : n ≤ 1)
  exact WithBot.coe_le_coe.2 this
