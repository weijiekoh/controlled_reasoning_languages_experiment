import Mathlib
open Polynomial
example : (X ^ 15 - 2 : (ZMod 7)[X]) = X ^ 15 - C 2 := by rw [map_ofNat C 2]
example : (X ^ 15 - 2 : (ZMod 7)[X]) = X ^ 15 - C 2 := by simp [map_ofNat]
example : ((15:ℕ) : ZMod 7) ≠ 0 := by decide
example : (2 : ZMod 7) ≠ 0 := by decide
