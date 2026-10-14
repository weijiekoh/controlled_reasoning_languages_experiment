import Mathlib

def switch_lamp (n : ℕ+) (switch_label : Fin (2 * n)) (lamps_state : List Bool) : List Bool :=
  List.mapIdx (fun j (x : Bool) => if j = switch_label then ¬x else x) lamps_state

def lamps_final_state (n : ℕ+) (switch_list : List (Fin (2 * n))) : List Bool :=
  match switch_list with
  | [] => (List.ofFn (fun _ : Fin (2 * n) => false))
  | h :: t => switch_lamp n h (lamps_final_state n t)

def final_goal (n : ℕ+) := List.ofFn (fun (i : Fin (2 * n)) => if i.val < n then true else false)

def N (n k : ℕ+) := @Finset.univ (Fin k → Fin (2 * n)) _ |>.filter
  (fun f => lamps_final_state n (List.ofFn f) = final_goal n) |>.card

def M (n k : ℕ+) := @Finset.univ (Fin k → Fin (2 * n)) _ |>.filter
  (fun f => ∀ (i : Fin k), f i < ⟨n.1, lt_two_mul_self n.2⟩) |>.filter
  (fun f => lamps_final_state n (List.ofFn f) = final_goal n) |>.card

noncomputable abbrev imo_2008_p5_solution : ℕ+ → ℕ+ → ℝ := fun n k => 2 ^ (k.1 - n.1)
