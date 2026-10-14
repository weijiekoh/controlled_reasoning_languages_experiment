import Mathlib
#check @RatFunc.eval
#check @RatFunc.eval_C
example (f : RatFunc ℚ) : True := by
  have := f.eval C f
  trivial
