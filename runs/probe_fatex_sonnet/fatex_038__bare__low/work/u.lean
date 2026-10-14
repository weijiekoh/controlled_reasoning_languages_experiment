import Mathlib
open Polynomial DualNumber
noncomputable section
set_option trace.Meta.synthInstance true in
example (k : Type) [Field k] (a : (DualNumber k)[X]): (Ideal.span {a}).IsTwoSided := inferInstance
