/have := (Real.hasDerivAt_rpow_const/,/simpa using (by simpa/c\
    have h3 := (((hasDerivAt_id (0:ℝ)).const_add 1).rpow_const (p := p) (Or.inr hp1))\
    simpa using h3
s/^    simpa using hbt.inv_tendsto_atTop/    simpa using tendsto_const_nhds.div_atTop (c := (1:ℝ)) hbt/
/^  rw \[div_pow, ← Real.rpow_natCast/,$c\
  have e : (a n ^ p) ^ k = a n ^ (k+1) := by\
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos n).le, ← Real.rpow_natCast]\
    congr 1\
    rw [hp]; push_cast; field_simp\
  rw [div_pow, e]
