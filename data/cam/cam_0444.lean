import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-444»

def linearFractionalMap
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d : ℝ) :
    {x : Fin n → ℝ // dotProduct c x + d > 0} → (Fin m → ℝ) :=
  fun x =>
    let denom : ℝ := dotProduct c x.1 + d
    fun i => ((∑ j : Fin n, A i j * x.1 j) + b i) / denom

private lemma linearFractionalMap_bottomRight_of_mul_eq_one
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin n → ℝ)
    (d : ℝ)
    (Ainv : Matrix (Fin n) (Fin n) ℝ)
    (binv cinv : Fin n → ℝ)
    (dinv : ℝ)
    (hQinv :
      Matrix.fromBlocks A (fun i _ => b i) (fun _ j => c j) (fun _ _ => d) *
        Matrix.fromBlocks Ainv (fun i _ => binv i) (fun _ j => cinv j) (fun _ _ => dinv) =
        (1 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)) :
    dotProduct c binv + d * dinv = 1 := by
  have h := congr_fun (congr_fun hQinv (Sum.inr ())) (Sum.inr ())
  simpa [Matrix.mul_apply, Matrix.fromBlocks, dotProduct] using h

private lemma linearFractionalMap_bottomLeft_of_mul_eq_one
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin n → ℝ)
    (d : ℝ)
    (Ainv : Matrix (Fin n) (Fin n) ℝ)
    (binv cinv : Fin n → ℝ)
    (dinv : ℝ)
    (hQinv :
      Matrix.fromBlocks A (fun i _ => b i) (fun _ j => c j) (fun _ _ => d) *
        Matrix.fromBlocks Ainv (fun i _ => binv i) (fun _ j => cinv j) (fun _ _ => dinv) =
        (1 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)) :
    ∀ j : Fin n, dotProduct c (fun i => Ainv i j) + d * cinv j = 0 := by
  intro j
  have h := congr_fun (congr_fun hQinv (Sum.inr ())) (Sum.inl j)
  simpa [Matrix.mul_apply, Matrix.fromBlocks, dotProduct] using h

private lemma linearFractionalMap_inverse_mem_domain
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin n → ℝ)
    (d : ℝ)
    (Ainv : Matrix (Fin n) (Fin n) ℝ)
    (binv cinv : Fin n → ℝ)
    (dinv : ℝ)
    (hQinv :
      Matrix.fromBlocks A (fun i _ => b i) (fun _ j => c j) (fun _ _ => d) *
        Matrix.fromBlocks Ainv (fun i _ => binv i) (fun _ j => cinv j) (fun _ _ => dinv) =
        (1 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ))
    (y : {y : Fin n → ℝ // dotProduct cinv y + dinv > 0}) :
    dotProduct c (linearFractionalMap Ainv binv cinv dinv y) + d > 0 := by
  let s : ℝ := dotProduct cinv y.1 + dinv
  have hs_pos : 0 < s := y.2
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hleft : ∀ j : Fin n, dotProduct c (fun i => Ainv i j) + d * cinv j = 0 :=
    linearFractionalMap_bottomLeft_of_mul_eq_one A b c d Ainv binv cinv dinv hQinv
  have hright : dotProduct c binv + d * dinv = 1 :=
    linearFractionalMap_bottomRight_of_mul_eq_one A b c d Ainv binv cinv dinv hQinv
  have hsum :
      (∑ i : Fin n, c i * ∑ j : Fin n, Ainv i j * y.1 j) =
        ∑ j : Fin n, y.1 j * ∑ i : Fin n, c i * Ainv i j := by
    calc
      (∑ i : Fin n, c i * ∑ j : Fin n, Ainv i j * y.1 j)
          = ∑ i : Fin n, ∑ j : Fin n, c i * (Ainv i j * y.1 j) := by
            simp [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ i : Fin n, c i * (Ainv i j * y.1 j) := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n, y.1 j * ∑ i : Fin n, c i * Ainv i j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  have hcoeff :
      (∑ i : Fin n, c i * ((∑ j : Fin n, Ainv i j * y.1 j) + binv i)) +
          d * ((∑ j : Fin n, cinv j * y.1 j) + dinv) = 1 := by
    calc
      (∑ i : Fin n, c i * ((∑ j : Fin n, Ainv i j * y.1 j) + binv i)) +
          d * ((∑ j : Fin n, cinv j * y.1 j) + dinv)
          = (∑ j : Fin n, y.1 j *
              (dotProduct c (fun i => Ainv i j) + d * cinv j)) +
              (dotProduct c binv + d * dinv) := by
            simp [dotProduct]
            calc
              ∑ x, c x * (∑ x_1, Ainv x x_1 * y.1 x_1 + binv x) +
                  d * (∑ x, cinv x * y.1 x + dinv)
                  = (∑ x, c x * ∑ x_1, Ainv x x_1 * y.1 x_1) +
                      (∑ x, c x * binv x) +
                      (d * ∑ x, cinv x * y.1 x + d * dinv) := by
                    simp [mul_add, Finset.sum_add_distrib]
              _ = (∑ x, y.1 x * ∑ x_1, c x_1 * Ainv x_1 x) +
                      (∑ x, c x * binv x) +
                      (d * ∑ x, cinv x * y.1 x + d * dinv) := by
                    rw [hsum]
              _ = ∑ x, y.1 x * (∑ x_1, c x_1 * Ainv x_1 x + d * cinv x) +
                      (∑ i, c i * binv i + d * dinv) := by
                    simp [mul_add, Finset.sum_add_distrib]
                    rw [Finset.mul_sum]
                    ring_nf
                    congr 1
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
      _ = 1 := by
            simp [hleft, hright]
  have hmap :
      dotProduct c (linearFractionalMap Ainv binv cinv dinv y) =
        (∑ i : Fin n, c i * ((∑ j : Fin n, Ainv i j * y.1 j) + binv i)) / s := by
    rw [show s = (∑ j : Fin n, cinv j * y.1 j) + dinv by simp [s, dotProduct]]
    simp [linearFractionalMap, dotProduct, div_eq_mul_inv]
    calc
      ∑ x, c x * ((∑ x_1, Ainv x x_1 * y.1 x_1 + binv x) *
          (∑ x, cinv x * y.1 x + dinv)⁻¹)
          = ∑ x, (c x * (∑ x_1, Ainv x x_1 * y.1 x_1 + binv x)) *
              (∑ x, cinv x * y.1 x + dinv)⁻¹ := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ x, c x * (∑ x_1, Ainv x x_1 * y.1 x_1 + binv x)) *
          (∑ x, cinv x * y.1 x + dinv)⁻¹ := by
            rw [Finset.sum_mul]
  have hmul :
      s * (dotProduct c (linearFractionalMap Ainv binv cinv dinv y) + d) = 1 := by
    rw [hmap]
    field_simp [hs_ne]
    rw [show s = (∑ j : Fin n, cinv j * y.1 j) + dinv by simp [s, dotProduct]]
    linarith [hcoeff]
  nlinarith

theorem linearFractionalMap_bijective_with_inverse
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin n → ℝ)
    (d : ℝ)
    (Ainv : Matrix (Fin n) (Fin n) ℝ)
    (binv cinv : Fin n → ℝ)
    (dinv : ℝ)
    (hQinv :
      Matrix.fromBlocks A (fun i _ => b i) (fun _ j => c j) (fun _ _ => d) *
        Matrix.fromBlocks Ainv (fun i _ => binv i) (fun _ j => cinv j) (fun _ _ => dinv) =
        (1 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ))
    (hQinv' :
      Matrix.fromBlocks Ainv (fun i _ => binv i) (fun _ j => cinv j) (fun _ _ => dinv) *
        Matrix.fromBlocks A (fun i _ => b i) (fun _ j => c j) (fun _ _ => d) =
        (1 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)) :
    Set.BijOn
        (fun x : {x : Fin n → ℝ // dotProduct c x + d > 0} =>
          linearFractionalMap A b c d x)
        Set.univ
        {y | dotProduct cinv y + dinv > 0} ∧
      (∀ y : {y : Fin n → ℝ // dotProduct cinv y + dinv > 0},
        linearFractionalMap A b c d
          ⟨linearFractionalMap Ainv binv cinv dinv y,
            by
              exact linearFractionalMap_inverse_mem_domain
                A b c d Ainv binv cinv dinv hQinv y⟩ = y.1) ∧
      (∀ x : {x : Fin n → ℝ // dotProduct c x + d > 0},
        linearFractionalMap Ainv binv cinv dinv
          ⟨linearFractionalMap A b c d x,
            by
              exact linearFractionalMap_inverse_mem_domain
                Ainv binv cinv dinv A b c d hQinv' x⟩ = x.1) := by
  sorry

end «CAM-Bench-444»
