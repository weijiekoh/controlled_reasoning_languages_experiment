s=open('amc12a_2020_p4.lean').read()
pf="""by
  have : S = (Finset.Icc 1000 9999).filter (fun n => (∀ d ∈ Nat.digits 10 n, Even d) ∧ 5 ∣ n) := by
    ext n
    rw [h₀]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    tauto
  rw [this]
  decide +kernel"""
open('amc12a_2020_p4.lean','w').write(s.replace("by sorry",pf))
