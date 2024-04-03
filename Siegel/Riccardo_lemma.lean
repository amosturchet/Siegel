import Mathlib

variable {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)

open Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

lemma foo {A : Type*} [Fintype A] (f : A → ℕ) : (sup univ f) = sup univ fun b ↦ (f b : NNReal) :=
  comp_sup_eq_sup_comp_of_is_total _ Nat.mono_cast (by simp)

lemma bar : ∃ (k : ℕ), ‖M‖ = k := by
  use sup univ fun b ↦ sup univ fun b' ↦ (M b b').natAbs
  simp_rw [norm_def, Pi.norm_def, Pi.nnnorm_def, ← NNReal.coe_nat_cast, foo]
  congr; ext; congr; ext
  simp [Nat.cast_natAbs, Int.norm_eq_abs]

section Mathlib
open Algebra Order Monoid WithZero

variable {M : Type*} [LinearOrderedCommMonoid M] {n m : ℕ} (A : Matrix (Fin m) (Fin n) M)

/- lemma foo' {A : Type*} [Fintype A] (f : A → M) : (sup univ f) = sup univ fun b ↦ (f b : NNReal) :=
  comp_sup_eq_sup_comp_of_is_total _ Nat.mono_cast (by simp) -/

end Mathlib
