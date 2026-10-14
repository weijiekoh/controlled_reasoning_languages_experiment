lemma strictprod (f g : ℂ → ℝ) (s : Multiset ℂ) (hs : s ≠ 0) (h0 : ∀ r ∈ s, 0 ≤ f r)
    (h : ∀ r ∈ s, f r < g r) : (s.map f).prod < (s.map g).prod := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have ha := h a (by simp)
    have h0a := h0 a (by simp)
    by_cases hs0 : s = 0
    · subst hs0; simpa using ha
    · have := ih hs0 (fun r hr => h0 r (by simp [hr])) (fun r hr => h r (by simp [hr]))
      have hp : 0 ≤ (s.map f).prod := Multiset.prod_nonneg (by
        intro x hx; obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx; exact h0 r (by simp [hr]))
      exact mul_lt_mul'' ha this h0a hp

lemma factor (P Q : Polynomial ℤ) (hP : P ≠ 0) (h : ∀ n, P.coeff n = 0 ∨ P.coeff n = 1)
    (hd : 0 < Q.degree) (hdiv : Q ∣ P) : 2 ≤ |Q.eval 2| := by
  obtain ⟨S, hS⟩ := hdiv
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hd
  set Qc := Q.map (Int.castRingHom ℂ) with hQc
  have hroot : ∀ r ∈ Qc.roots, r.re < 3/2 := by
    intro r hr
    have hr' := (Polynomial.mem_roots (by simpa [hQc] using hQ0)).1 hr
    apply rootre P hP h
    rw [hS, map_mul]
    have : Polynomial.aeval r Q = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hr'
    rw [this, zero_mul]
  have hev : ∀ w : ℂ, Qc.eval w = (Qc.leadingCoeff) * (Qc.roots.map (fun r => w - r)).prod := by
    intro w
    conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := Qc))]
    simp [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def]
  have hne : Qc.roots ≠ 0 := by
    intro h0
    have := IsAlgClosed.card_roots_eq_natDegree (p := Qc)
    rw [h0] at this
    have h2 : Qc.natDegree = Q.natDegree := Polynomial.natDegree_map_eq_of_injective (by exact_mod_cast Int.cast_injective) _
    have := Polynomial.natDegree_pos_iff_degree_pos.2 hd
    simp at *; omega
  have hlt : ((Qc.roots.map (fun r => (1:ℂ) - r)).map (‖·‖)).prod < ((Qc.roots.map (fun r => (2:ℂ) - r)).map (‖·‖)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    apply strictprod (fun r => ‖(1:ℂ) - r‖) (fun r => ‖(2:ℂ) - r‖) _ hne (fun _ _ => norm_nonneg _)
    intro r hr
    have := hroot r hr
    apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  have hQ1 : Q.eval 1 ≠ 0 := by
    intro h0
    have : Polynomial.aeval (1:ℂ) P = 0 := by
      rw [hS, map_mul, Polynomial.aeval_def, Polynomial.eval₂_at_one]
      simp [h0]
    have := rootre P hP h 1 this
    norm_num at this
  have e1 : (Q.eval 1 : ℂ) = Qc.eval 1 := by simp [hQc]
  have e2 : (Q.eval 2 : ℂ) = Qc.eval 2 := by simp [hQc]
  have n1 : |(Q.eval 1 : ℝ)| = ‖Qc.eval 1‖ := by
    rw [← e1]; simp
  have n2 : |(Q.eval 2 : ℝ)| = ‖Qc.eval 2‖ := by
    rw [← e2]; simp
  rw [hev, norm_mul, Multiset.norm_prod] at n1 n2
  sorry
