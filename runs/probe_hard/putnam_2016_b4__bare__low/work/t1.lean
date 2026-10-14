import Mathlib


def vv (b : Bool) : ℝ := if b then 1 else 0

lemma two_coord {ι : Type} [Fintype ι] [DecidableEq ι] (p q : ι) (hpq : p ≠ q)
    (φ : Bool → Bool → ℝ) (G : (ι → Bool) → ℝ)
    (hG : ∀ f b c, G (Function.update (Function.update f p b) q c) = G f) :
    ∑ f, φ (f p) (f q) * G f = (1/4) * (∑ b, ∑ c, φ b c) * ∑ f, G f := by
  have hN : ∀ b c : Bool, ∑ f : ι → Bool, (if f p = b ∧ f q = c then G f else 0)
      = ∑ f : ι → Bool, (if f p = false ∧ f q = false then G f else 0) := by
    intro b c
    let ψ : (ι → Bool) → (ι → Bool) := fun f => Function.update (Function.update f p (xor (f p) b)) q (xor (f q) c)
    have hψ : ∀ f, ψ (ψ f) = f := by
      intro f; funext x
      by_cases hxq : x = q
      · subst hxq; simp [ψ, Function.update, hpq.symm]
      · by_cases hxp : x = p
        · subst hxp; simp [ψ, Function.update, hxq]
        · simp [ψ, Function.update, hxq, hxp]
    let e : (ι → Bool) ≃ (ι → Bool) := ⟨ψ, ψ, hψ, hψ⟩
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro f _
    have h1 : e f p = xor (f p) b := by simp [e, ψ, Function.update, hpq]
    have h2 : e f q = xor (f q) c := by simp [e, ψ, Function.update]
    have h3 : G (e f) = G f := hG f _ _
    rw [h1, h2, h3]
    cases b <;> cases c <;> cases hp : f p <;> cases hq : f q <;> simp
  have hsum : ∑ f, G f = 4 * ∑ f : ι → Bool, (if f p = false ∧ f q = false then G f else 0) := by
    have : ∀ f, G f = ∑ b, ∑ c, (if f p = b ∧ f q = c then G f else 0) := by
      intro f
      cases hp : f p <;> cases hq : f q <;> simp
    calc ∑ f, G f = ∑ f, ∑ b, ∑ c, (if f p = b ∧ f q = c then G f else 0) :=
          Finset.sum_congr rfl (fun f _ => this f)
      _ = ∑ b, ∑ c, ∑ f : ι → Bool, (if f p = b ∧ f q = c then G f else 0) := by
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
          rw [Finset.sum_comm]
      _ = _ := by
          simp only [hN]; simp; ring
  have : ∀ f : ι → Bool, φ (f p) (f q) * G f = ∑ b, ∑ c, φ b c * (if f p = b ∧ f q = c then G f else 0) := by
    intro f
    cases hp : f p <;> cases hq : f q <;> simp
  calc ∑ f, φ (f p) (f q) * G f = ∑ f, ∑ b, ∑ c, φ b c * (if f p = b ∧ f q = c then G f else 0) :=
        Finset.sum_congr rfl (fun f _ => this f)
    _ = ∑ b, ∑ c, φ b c * ∑ f : ι → Bool, (if f p = b ∧ f q = c then G f else 0) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]
    _ = _ := by
        simp only [hN, hsum, ← Finset.sum_mul, ← Finset.sum_mul]
        simp [← Finset.sum_mul]; ring_nf
