    have hlt : ∀ a ∈ A, a < 2021 := by
      intro a ha
      have ha' := (hm a).1 ha
      rcases lt_or_eq_of_le ha'.2.1 with h | h
      · exact h
      · subst h; simp at ha'
    have hinj : Set.InjOn (fun n => (g * n) % 2021) (A : Set ℕ) := by
      intro a ha b hb hab
      have h1 : g * a ≡ g * b [MOD 2021] := hab
      have h2 := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.gcd_comm] using hg) h1
      exact Nat.ModEq.eq_of_lt_of_lt h2 (hlt a ha) (hlt b hb)
    have hmaps : ∀ n ∈ A, (g * n) % 2021 ∈ A := by
      intro n hn
      have hn' := (hm n).1 hn
      have hc : Nat.gcd ((g * n) % 2021) 2021 = 1 := by
        have : Nat.Coprime (g * n) 2021 := Nat.Coprime.mul_left hg hn'.2.2
        have h3 := Nat.gcd_rec 2021 (g * n)
        rw [Nat.gcd_comm] at h3
        rw [← h3]; exact this
      rw [hm]
      refine ⟨?_, (Nat.mod_lt _ (by norm_num)).le, hc⟩
      rcases Nat.eq_zero_or_pos ((g * n) % 2021) with h | h
      · rw [h] at hc; simp at hc
      · exact h
    have himg : A.image (fun n => (g * n) % 2021) = A := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
        exact hmaps n hn
      · rw [Finset.card_image_of_injOn hinj]
    set T : ZMod p := ∑ n ∈ A, (n : ZMod p) ^ j with hT
    have hshift : T = (g : ZMod p) ^ j * T := by
      conv_lhs => rw [hT, ← himg]
      rw [Finset.sum_image hinj, hT, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have : (((g * n) % 2021 : ℕ) : ZMod p) = (g : ZMod p) * n := by
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.mod_modEq _ _).of_dvd hp)]
        push_cast; rfl
      simp only [this, mul_pow]
    have hg0 : (g : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hp hg).symm hd
      exact (Fact.out : p.Prime).one_lt.ne' this
    have hne : (g : ZMod p) ^ j ≠ 1 := by
      intro h1
      apply hd
      have hp1 : (g : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hg0
      have : (g : ZMod p) ^ (j % (p - 1)) = 1 := by
        rw [← Nat.mod_add_div j (p - 1), pow_add, pow_mul, hp1, one_pow, mul_one] at h1
        exact h1
      have hr := hord _ (Nat.mod_lt _ (by have := (Fact.out : p.Prime).two_le; omega)) this
      exact Nat.dvd_of_mod_eq_zero hr
    have : ((g : ZMod p) ^ j - 1) * T = 0 := by
      rw [sub_mul, ← hshift]; simp
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h

lemma o43 : ∀ r < 43 - 1, ((3 : ℕ) : ZMod 43)^r = 1 → r = 0 := by decide +kernel
lemma o47 : ∀ r < 47 - 1, ((5 : ℕ) : ZMod 47)^r = 1 → r = 0 := by decide +kernel
