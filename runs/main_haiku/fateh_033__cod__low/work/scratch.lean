import Mathlib
open Polynomial
example (f : ℚ[X]) (hf0 : f ≠ 0) (a : f.SplittingField) (ha : aeval a f = 0) (σ : f.Gal) : True := by
  have : Fact (map (algebraMap ℚ f.SplittingField) f).Splits := ⟨SplittingField.splits f⟩
  let a' : f.rootSet f.SplittingField := ⟨a, mem_rootSet.2 ⟨hf0, ha⟩⟩
  have hval : ∀ y : f.rootSet f.SplittingField, ((Gal.rootsEquivRoots f f.SplittingField) y).1 = y.1 := by
    intro y
    show (algebraMap f.SplittingField f.SplittingField) y.1 = y.1
    simp
  have hy : ((Gal.rootsEquivRoots f f.SplittingField).symm a').1 = a :=
    (hval _).symm.trans (congrArg Subtype.val ((Gal.rootsEquivRoots f f.SplittingField).apply_symm_apply a'))
  have key : ((σ • a' : f.rootSet f.SplittingField) : f.SplittingField) = σ a := by
    rw [Gal.smul_def]
    refine (hval _).trans ?_
    show σ ((Gal.rootsEquivRoots f f.SplittingField).symm a').1 = σ a
    rw [hy]
  trivial
