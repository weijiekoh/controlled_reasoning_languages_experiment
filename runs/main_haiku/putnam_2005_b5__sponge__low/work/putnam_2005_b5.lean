import Mathlib

open Nat Set

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
  obtain ⟨w, hw⟩ : ∃ w : (Fin n →₀ ℕ) → ℝ, ∀ α, w α = ∏ j, (((α j).factorial : ℕ) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ → ℝ,
      ∀ f g, B f g = ∑ α ∈ f.support, f.coeff α * w α * g.coeff α :=
    ⟨_, fun _ _ => rfl⟩
  have hw0 : ∀ α, 0 ≤ w α := fun α => by
    rw [hw]; exact Finset.prod_nonneg (fun j _ => Nat.cast_nonneg _)
  have hwpos : ∀ α, 0 < w α := fun α => by
    rw [hw]; exact Finset.prod_pos (fun j _ => by exact_mod_cast Nat.factorial_pos _)
  have hBfin : ∀ f g (S : Finset (Fin n →₀ ℕ)), f.support ⊆ S →
      B f g = ∑ α ∈ S, f.coeff α * w α * g.coeff α := by
    intro f g S hS
    rw [hB]
    apply Finset.sum_subset hS
    intro x _ hx
    rw [MvPolynomial.notMem_support_iff] at hx
    rw [hx, zero_mul, zero_mul]
  have hBr : ∀ f g h, B f (g + h) = B f g + B f h := by
    intro f g h
    simp only [hB, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]
  have hBl : ∀ f g h, B (f + g) h = B f h + B g h := by
    intro f g h
    have hS : (f + g).support ∪ f.support ∪ g.support ⊆ (f + g).support ∪ f.support ∪ g.support := le_refl _
    rw [hBfin (f + g) h ((f + g).support ∪ f.support ∪ g.support) (by intro x hx; simp only [Finset.mem_union]; tauto),
      hBfin f h ((f + g).support ∪ f.support ∪ g.support) (by intro x hx; simp only [Finset.mem_union]; tauto),
      hBfin g h ((f + g).support ∪ f.support ∪ g.support) (by intro x hx; simp only [Finset.mem_union]; tauto),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [MvPolynomial.coeff_add]
    ring
  have hB0 : ∀ g, B 0 g = 0 := fun g => by simp [hB]
  have hBr0 : ∀ f, B f 0 = 0 := fun f => by simp [hB]
  have hBmono : ∀ γ c g, B (MvPolynomial.monomial γ c) g = c * w γ * g.coeff γ := by
    intro γ c g
    rw [hBfin _ _ {γ} (MvPolynomial.support_monomial_subset)]
    simp
  have hwS : ∀ (i : Fin n) (β : Fin n →₀ ℕ), w (Finsupp.single i 1 + β) = w β * ((β i : ℝ) + 1) := by
    intro i β
    have h1 : ∏ j, (((((Finsupp.single i 1 : Fin n →₀ ℕ) + β) j).factorial : ℕ) : ℝ)
        = ((((β i + 1).factorial : ℕ)) : ℝ) * ∏ j ∈ Finset.univ.erase i, (((β j).factorial : ℕ) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · simp [add_comm]
      · apply Finset.prod_congr rfl
        intro j hj
        have : j ≠ i := Finset.ne_of_mem_erase hj
        simp [Finsupp.single_apply, this]
    have h2 : ∏ j, (((β j).factorial : ℕ) : ℝ)
        = (((β i).factorial : ℕ) : ℝ) * ∏ j ∈ Finset.univ.erase i, (((β j).factorial : ℕ) : ℝ) :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
    rw [hw, hw, h1, h2, Nat.factorial_succ]
    push_cast
    ring
  have hadj : ∀ (i : Fin n) (Q P : MvPolynomial (Fin n) ℝ),
      B (MvPolynomial.X i * Q) P = B Q (MvPolynomial.pderiv i P) := by
    intro i Q P
    induction Q using MvPolynomial.induction_on' with
    | monomial β c =>
      induction P using MvPolynomial.induction_on' with
      | monomial γ d =>
        rw [MvPolynomial.X, MvPolynomial.monomial_mul, MvPolynomial.pderiv_monomial, hBmono, hBmono]
        rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial, hwS]
        by_cases hγ : γ = Finsupp.single i 1 + β
        · subst hγ
          simp [add_tsub_cancel_left] <;> ring
        · by_cases h2 : γ - Finsupp.single i 1 = β
          · have hz : γ i = 0 := by
              by_contra hz
              apply hγ
              rw [← h2]
              ext j
              by_cases hj : j = i
              · subst hj
                simp [Finsupp.single_apply]
                omega
              · simp [Finsupp.single_apply, hj]
            simp [hγ, h2, hz]
          · simp [hγ, h2]
      | add p q hp hq => rw [map_add, hBr, hBr, hp, hq]
    | add p q hp hq => rw [mul_add, hBl, hp, hq, hBl]
  have hBsumL : ∀ (s : Finset (Fin n)) (F : Fin n → MvPolynomial (Fin n) ℝ) (g : MvPolynomial (Fin n) ℝ),
      B (∑ i ∈ s, F i) g = ∑ i ∈ s, B (F i) g := by
    intro s F g
    induction s using Finset.induction_on with
    | empty => simp [hB0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hBl, ih]
  have hBsumR : ∀ (s : Finset (Fin n)) (F : Fin n → MvPolynomial (Fin n) ℝ) (f : MvPolynomial (Fin n) ℝ),
      B f (∑ i ∈ s, F i) = ∑ i ∈ s, B f (F i) := by
    intro s F f
    induction s using Finset.induction_on with
    | empty => simp [hBr0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hBr, ih]
  have hdL : ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P) = 0 := by
    have e : ∀ i : Fin n, (MvPolynomial.pderiv i)^[2] P = MvPolynomial.pderiv i (MvPolynomial.pderiv i P) :=
      fun i => rfl
    simpa [e] using hderiv
  have hBPP0 : B P P = 0 := by
    obtain ⟨Q, hQ⟩ := hsumsq
    have e2 : ∑ i : Fin n, MvPolynomial.X i ^ 2 * Q = P := by
      rw [← Finset.sum_mul]; exact hQ.symm
    calc B P P = B (∑ i : Fin n, MvPolynomial.X i ^ 2 * Q) P := by rw [e2]
      _ = ∑ i : Fin n, B (MvPolynomial.X i ^ 2 * Q) P := hBsumL _ _ _
      _ = ∑ i : Fin n, B Q (MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) :=
          Finset.sum_congr rfl (fun i _ => by rw [pow_two, mul_assoc, hadj, hadj])
      _ = B Q (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) := (hBsumR _ _ _).symm
      _ = 0 := by rw [hdL]; exact hBr0 Q
  have hsupp : P.support = ∅ := by
    by_contra hne
    obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hnn : ∀ β ∈ P.support, 0 ≤ P.coeff β * w β * P.coeff β := fun β _ => by
      have : P.coeff β * w β * P.coeff β = w β * (P.coeff β * P.coeff β) := by ring
      rw [this]; exact mul_nonneg (hw0 β) (mul_self_nonneg _)
    have hS := hBPP0
    rw [hB] at hS
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS α hα
    have hc : P.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    exact mul_ne_zero (mul_ne_zero hc (hwpos α).ne') hc hz
  exact MvPolynomial.support_eq_empty.mp hsupp
