import Mathlib

noncomputable abbrev brualdi_ch7_15_solution : PowerSeries ℝ := PowerSeries.X * (PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1) * PowerSeries.inv (1 - PowerSeries.X) ^ 4

/--
Determine the generating function for the sequence of cubes \[ 0, 1, 8, \ldots, n^{3}, \ldots \]
-/
theorem brualdi_ch7_15 : PowerSeries.mk (fun (n : ℕ) => (n : ℝ) ^ 3) = brualdi_ch7_15_solution := by
    sorry
