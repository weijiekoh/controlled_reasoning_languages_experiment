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
  classical

  let w : (Fin n →₀ ℕ) → ℝ := fun a => ∏ j, (((a j).factorial : ℕ) : ℝ)
  let W : MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ → ℝ := fun f g =>
    ∑ᶠ a : Fin n →₀ ℕ, w a * MvPolynomial.coeff a f * MvPolynomial.coeff a g
  have hwpos : ∀ a, 0 < w a := fun a => Finset.prod_pos (fun j _ => by exact_mod_cast Nat.factorial_pos _)
  have hfin : ∀ f g : MvPolynomial (Fin n) ℝ,
      (Function.support fun a => w a * MvPolynomial.coeff a f * MvPolynomial.coeff a g).Finite := by
    intro f g
    apply (f.support.finite_toSet).subset
    intro a ha
    simp only [Function.mem_support] at ha
    simp only [Finset.mem_coe, MvPolynomial.mem_support_iff]
    intro h0; apply ha; simp [h0]
  have hWadd_r : ∀ f g1 g2, W f (g1 + g2) = W f g1 + W f g2 := by
    intro f g1 g2
    simp only [W, MvPolynomial.coeff_add]
    rw [← finsum_add_distrib (hfin f g1) (hfin f g2)]
    apply finsum_congr; intro a; ring
  have hWadd_l : ∀ f1 f2 g, W (f1 + f2) g = W f1 g + W f2 g := by
    intro f1 f2 g
    simp only [W, MvPolynomial.coeff_add]
    rw [← finsum_add_distrib (hfin f1 g) (hfin f2 g)]
    apply finsum_congr; intro a; ring
  have hWzero_r : ∀ f, W f 0 = 0 := by intro f; simp [W]
  have hWzero_l : ∀ g, W 0 g = 0 := by intro g; simp [W]
  have hWsum_r : ∀ (f : MvPolynomial (Fin n) ℝ) (s : Finset (Fin n)) (g : Fin n → MvPolynomial (Fin n) ℝ),
      W f (∑ i ∈ s, g i) = ∑ i ∈ s, W f (g i) := by
    intro f s g
    refine Finset.induction_on s ?_ ?_
    · simp [hWzero_r]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hWadd_r, ih]
  have hWsum_l : ∀ (s : Finset (Fin n)) (g : Fin n → MvPolynomial (Fin n) ℝ) (h : MvPolynomial (Fin n) ℝ),
      W (∑ i ∈ s, g i) h = ∑ i ∈ s, W (g i) h := by
    intro s g h
    refine Finset.induction_on s ?_ ?_
    · simp [hWzero_l]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hWadd_l, ih]
  have hWpos : ∀ f, W f f = 0 → f = 0 := by
    intro f hf
    apply MvPolynomial.ext
    intro a
    simp only [MvPolynomial.coeff_zero]
    have hsub : Function.support (fun b => w b * MvPolynomial.coeff b f * MvPolynomial.coeff b f)
        ⊆ (f.support : Set (Fin n →₀ ℕ)) := by
      intro b hb
      simp only [Function.mem_support] at hb
      simp only [Finset.mem_coe, MvPolynomial.mem_support_iff]
      intro h0; apply hb; simp [h0]
    simp only [W] at hf
    rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_eq_zero_iff_of_nonneg] at hf
    · by_cases ha : a ∈ f.support
      · have h1 := hf a ha
        have h2 : w a * (MvPolynomial.coeff a f * MvPolynomial.coeff a f) = 0 := by
          rw [← h1]; ring
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h (hwpos a).ne'
        · exact mul_self_eq_zero.1 h
      · by_contra h
        exact ha (MvPolynomial.mem_support_iff.2 h)
    · intro b _
      have := hwpos b
      have h3 : w b * MvPolynomial.coeff b f * MvPolynomial.coeff b f
          = w b * (MvPolynomial.coeff b f * MvPolynomial.coeff b f) := by ring
      rw [h3]
      exact mul_nonneg this.le (mul_self_nonneg _)
  have hw : ∀ (a : Fin n →₀ ℕ) (i : Fin n), w (a + Finsupp.single i 1) = w a * ((a i : ℝ) + 1) := by
    intro a i
    simp only [w]
    have split : ∀ F : Fin n → ℝ, ∏ j, F j = F i * ∏ j ∈ Finset.univ.erase i, F j :=
      fun F => (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [split, split (fun j => (((a j).factorial : ℕ) : ℝ))]
    have h1 : ((a + Finsupp.single i 1 : Fin n →₀ ℕ) i).factorial = (a i + 1) * (a i).factorial := by
      simp [Nat.factorial_succ]
    have h2 : ∏ j ∈ Finset.univ.erase i, (((a + Finsupp.single i 1 : Fin n →₀ ℕ) j).factorial : ℝ)
        = ∏ j ∈ Finset.univ.erase i, (((a j).factorial : ℕ) : ℝ) :=
      Finset.prod_congr rfl (fun j hj => by simp [Finsupp.single_apply, Finset.ne_of_mem_erase hj])
    rw [h2, h1]
    push_cast
    ring
  have hA : ∀ (f g : MvPolynomial (Fin n) ℝ) (i : Fin n),
      W f (MvPolynomial.pderiv i g) = W (MvPolynomial.X i * f) g := by
    intro f g i
    simp only [W]
    have key : ∀ a : Fin n →₀ ℕ,
        w a * MvPolynomial.coeff a f * MvPolynomial.coeff a (MvPolynomial.pderiv i g)
          = w (a + Finsupp.single i 1) * MvPolynomial.coeff (a + Finsupp.single i 1) (MvPolynomial.X i * f)
              * MvPolynomial.coeff (a + Finsupp.single i 1) g := by
      intro a
      have hmem : i ∈ (a + Finsupp.single i 1 : Fin n →₀ ℕ).support := by simp
      rw [MvPolynomial.coeff_X_mul', if_pos hmem, add_tsub_cancel_right, hw, MvPolynomial.coeff_pderiv]
      ring
    rw [finsum_congr key]
    have hS : ∀ b : Fin n →₀ ℕ, b ∉ Set.range (fun a : Fin n →₀ ℕ => a + Finsupp.single i 1) →
        w b * MvPolynomial.coeff b (MvPolynomial.X i * f) * MvPolynomial.coeff b g = 0 := by
      intro b hb
      have hbi : b i = 0 := by
        by_contra h
        have hle : Finsupp.single i 1 ≤ b := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
        exact hb ⟨b - Finsupp.single i 1, tsub_add_cancel_of_le hle⟩
      simp [MvPolynomial.coeff_X_mul', hbi]
    have e1 : ∑ᶠ b, w b * MvPolynomial.coeff b (MvPolynomial.X i * f) * MvPolynomial.coeff b g
        = ∑ᶠ b ∈ Set.range (fun a : Fin n →₀ ℕ => a + Finsupp.single i 1),
            w b * MvPolynomial.coeff b (MvPolynomial.X i * f) * MvPolynomial.coeff b g := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro b
      by_cases hb : b ∈ Set.range (fun a : Fin n →₀ ℕ => a + Finsupp.single i 1)
      · simp [Set.indicator_apply, hb]
      · simp [Set.indicator_apply, hb, hS b hb]
    have hbij : Set.BijOn (fun a : Fin n →₀ ℕ => a + Finsupp.single i 1) Set.univ
        (Set.range (fun a : Fin n →₀ ℕ => a + Finsupp.single i 1)) := by
      rw [← Set.image_univ]
      exact (add_left_injective (Finsupp.single i 1)).injOn.bijOn_image
    rw [e1, ← finsum_mem_univ]
    exact finsum_mem_eq_of_bijOn _ hbij (fun x _ => rfl)
  obtain ⟨R, hR⟩ := hsumsq
  subst hR
  have hi : ∀ (i : Fin n) (h : MvPolynomial (Fin n) ℝ),
      W R (MvPolynomial.pderiv i (MvPolynomial.pderiv i h)) = W (MvPolynomial.X i * (MvPolynomial.X i * R)) h := by
    intro i h
    rw [hA R (MvPolynomial.pderiv i h) i, hA (MvPolynomial.X i * R) h i]
  have hsum : ∑ i : Fin n, MvPolynomial.X i * (MvPolynomial.X i * R)
      = (∑ i : Fin n, MvPolynomial.X i ^ 2) * R := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hL : ∀ h : MvPolynomial (Fin n) ℝ,
      W R (∑ i : Fin n, (MvPolynomial.pderiv i)^[2] h)
        = W (∑ i : Fin n, MvPolynomial.X i * (MvPolynomial.X i * R)) h := by
    intro h
    rw [hWsum_r, hWsum_l]
    apply Finset.sum_congr rfl
    intro i _
    exact hi i h
  have main : W R (∑ i : Fin n, (MvPolynomial.pderiv i)^[2] ((∑ i : Fin n, MvPolynomial.X i ^ 2) * R))
      = W ((∑ i : Fin n, MvPolynomial.X i ^ 2) * R) ((∑ i : Fin n, MvPolynomial.X i ^ 2) * R) := by
    rw [hL, hsum]
  have h0 : W R (∑ i : Fin n, (MvPolynomial.pderiv i)^[2] ((∑ i : Fin n, MvPolynomial.X i ^ 2) * R)) = 0 := by
    rw [hderiv, hWzero_r]
  exact hWpos _ (by rw [← main]; exact h0)
