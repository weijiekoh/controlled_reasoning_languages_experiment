import Mathlib
open Matrix
example (p : ℕ) [Fact p.Prime] (a d : (ZMod p)ˣ) (b t : ZMod p) : !![(a : ZMod p), b; 0, d] * !![1,t;0,1] = !![1,((a:ZMod p) * t * (d⁻¹ : (ZMod p)ˣ));0,1] * !![(a : ZMod p), b; 0, d] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
  trace_state
  sorry
