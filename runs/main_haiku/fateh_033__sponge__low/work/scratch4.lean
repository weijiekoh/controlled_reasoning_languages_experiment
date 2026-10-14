import Mathlib
open Polynomial
example (f : ℚ[X]) (n : ℕ) (hf : f.degree = n) (hf' : Irreducible f) : Nat.card (f.rootSet f.SplittingField) = n := by
  have := card_rootSet_eq_natDegree hf'.separable (SplittingField.splits f)
  rw [natDegree_eq_of_degree_eq_some hf] at this
  rw [Nat.card_eq_fintype_card]
  exact this
example (f : ℚ[X]) (g : f.Gal) (a b : f.SplittingField) (ha' : a ∈ f.rootSet f.SplittingField) (hb' : b ∈ f.rootSet f.SplittingField) :
    g a = b ↔ g • (⟨a, ha'⟩ : f.rootSet f.SplittingField) = ⟨b, hb'⟩ := by
  rw [Subtype.ext_iff]
  exact Iff.rfl
