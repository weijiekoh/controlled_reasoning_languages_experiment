import Mathlib
open Equiv

def τ : Perm (Fin 4) := swap 0 1 * swap 2 3
def ρ : Perm (Fin 4) := swap 0 2 * swap 2 1 * swap 1 3
def ψf : DihedralGroup 4 → Perm (Fin 4)
  | .r i => ρ ^ i.val
  | .sr i => swap 0 1 * ρ ^ i.val

def ψ : DihedralGroup 4 →* Perm (Fin 4) :=
  MonoidHom.mk' ψf (by decide)

theorem ψinj : Function.Injective ψ := by decide

theorem ψrange : ∀ σ : Perm (Fin 4), σ * τ = τ * σ → ∃ x, ψ x = σ := by decide
theorem ψcomm : ∀ x, ψ x * τ = τ * ψ x := by decide
