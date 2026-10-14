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
    have hr' := (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (RingHom.injective_int (Int.castRingHom ℂ))).2 hQ0)).1 hr
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
  have hnp : ∀ s : Multiset ℂ, ‖s.prod‖ = (s.map (‖·‖)).prod := by
    intro s
    have := map_multiset_prod (normHom (α := ℂ)) s
    simpa using this
  have hP1 : 0 < P.eval 1 := by
    have hl : P.coeff P.natDegree = 1 := by
      rcases h P.natDegree with h | h
      · exact absurd (by simpa using h) (by simpa [Polynomial.leadingCoeff] using hP)
      · exact h
    rw [Polynomial.eval_eq_sum_range]
    have := Finset.single_le_sum (f := fun i => P.coeff i * (1:ℤ)^i) (s := Finset.range (P.natDegree+1))
      (fun i _ => by rcases h i with h | h <;> simp [h]) (a := P.natDegree) (by simp)
    simp [hl] at this ⊢
    omega
  have hQ1 : Q.eval 1 ≠ 0 := by
    intro h0
    have : P.eval 1 = 0 := by rw [hS]; simp [h0]
    omega
  have e1 : Qc.eval 1 = ((Q.eval 1 : ℤ) : ℂ) := by
    rw [hQc, show (1:ℂ) = ((1:ℤ):ℂ) by simp, Polynomial.eval_intCast_map]; simp
  have e2 : Qc.eval 2 = ((Q.eval 2 : ℤ) : ℂ) := by
    have := Polynomial.eval_intCast_map (Int.castRingHom ℂ) Q 2
    simpa using this
  have n1 : ((|Q.eval 1| : ℤ) : ℝ) = ‖Qc.leadingCoeff‖ * ((Qc.roots.map (fun r => (1:ℂ) - r)).map (‖·‖)).prod := by
    rw [← hnp, ← norm_mul, ← hev, e1]; simp
  have n2 : ((|Q.eval 2| : ℤ) : ℝ) = ‖Qc.leadingCoeff‖ * ((Qc.roots.map (fun r => (2:ℂ) - r)).map (‖·‖)).prod := by
    rw [← hnp, ← norm_mul, ← hev, e2]; simp
  have hpos : (1:ℝ) ≤ ((|Q.eval 1| : ℤ) : ℝ) := by
    exact_mod_cast Int.one_le_abs hQ1
  have hA : 0 ≤ ((Qc.roots.map (fun r => (1:ℂ) - r)).map (‖·‖)).prod := by
    apply Multiset.prod_nonneg
    intro x hx; obtain ⟨r, _, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg _
  have hL : 0 < ‖Qc.leadingCoeff‖ := by
    rcases (norm_nonneg Qc.leadingCoeff).lt_or_eq with h | h
    · exact h
    · rw [n1, ← h] at hpos; simp at hpos; linarith
  have : |Q.eval 1| < |Q.eval 2| := by
    have : ((|Q.eval 1| : ℤ) : ℝ) < ((|Q.eval 2| : ℤ) : ℝ) := by
      rw [n1, n2]; exact mul_lt_mul_of_pos_left hlt hL
    exact_mod_cast this
  have := Int.one_le_abs hQ1
  omega

theorem putnam_2021_a6 :
  (∀ P, (∀ n : ℕ, P.coeff n = 0 ∨ P.coeff n = 1) →
    (∃ Q R : Polynomial ℤ, Q.degree > 0 ∧ R.degree > 0 ∧ P = Q * R) →
    (P.eval 2 ≠ 0 ∧ P.eval 2 ≠ 1 ∧ ¬Prime (P.eval 2)))
  ↔ True := by
  refine ⟨fun _ => trivial, fun _ P hc ⟨Q, R, hQ, hR, hPQR⟩ => ?_⟩
  have hP : P ≠ 0 := by
    rintro rfl
    have := hPQR.symm
    rcases mul_eq_zero.1 this with h | h <;> simp [h] at hQ hR
  have a := factor P Q hP hc hQ ⟨R, hPQR⟩
  have b := factor P R hP hc hR ⟨Q, by rw [hPQR, mul_comm]⟩
  have hv : P.eval 2 = Q.eval 2 * R.eval 2 := by rw [hPQR]; simp
  have hab : 4 ≤ |P.eval 2| := by
    rw [hv, abs_mul]; nlinarith
  refine ⟨by intro h; rw [h] at hab; simp at hab, by intro h; rw [h] at hab; simp at hab, ?_⟩
  intro hp
  rw [hv] at hp
  rcases hp.irreducible.isUnit_or_isUnit rfl with u | u
  · have := Int.isUnit_iff.1 u
    rcases this with h | h <;> rw [h] at a <;> simp at a
  · have := Int.isUnit_iff.1 u
    rcases this with h | h <;> rw [h] at b <;> simp at b
