s=open('t.lean').read()
s=s.replace("  let K := AdjoinRoot f\n","  let K := AdjoinRoot f\n  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2\n")
s=s.replace("  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2\n  have hr2","  have hr2")
s=s.replace("    simpa [hfdef, add_assoc, eq_neg_iff_add_eq_zero] using h","    have h' : r ^ 2 ^ n + (r + 1) = 0 := by simpa [hfdef, add_assoc] using h\n    exact CharTwo.add_eq_zero.mp h'")
s=s.replace("simpa [ψa, ψ] using hr2","simpa [ψa, ψ, iterateFrobenius_def] using hr2")
s=s.replace("simpa [ψa, ψ] using this","simpa [ψa, ψ, iterateFrobenius_def] using this")
s=s.replace("    rw [Nat.card_eq_fintype_card] at this\n    rw [this, (","    rw [this, ZMod.card, (")
a=s.index("  have hne"); b=s.index("  have hle")
s=s[:a]+"""  have hnd : (X ^ 2 ^ (2*n) - X : K[X]).natDegree = 2 ^ (2*n) := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
    exact Nat.one_lt_two_pow (by omega)
  have hne : (X ^ 2 ^ (2*n) - X : K[X]) ≠ 0 := by
    intro h
    rw [h] at hnd
    simp at hnd
    exact absurd hnd.symm (by positivity)
"""+s[b:]
s=s.replace("  rw [natDegree_sub_eq_left_of_natDegree_lt (by simp; exact Nat.one_lt_two_pow (by omega))] at hle\n","  rw [hnd] at hle\n")
a=s.index("  have h1")
s=s[:a]+"""  have h1 : ∀ m, 3 ≤ m → 2 * m < 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  have h2 := h1 n hn
  have : 2 ^ (2*n) < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) h2
  omega
"""
open('t.lean','w').write(s)
