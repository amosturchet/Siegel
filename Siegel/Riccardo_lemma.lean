import Mathlib.Analysis.Matrix

variable {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)

open Matrix Set Finset

attribute [local instance] Matrix.seminormedAddCommGroup

lemma bar {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℤ) : ∃ (k : ℕ), ‖f‖ = k := by
  simp_rw [Pi.norm_def, Pi.nnnorm_def]
  use sup univ fun b ↦ sup univ fun b' ↦ (f b b').natAbs
  rw [← NNReal.coe_nat_cast, NNReal.coe_inj]
  have : (sup Finset.univ fun b ↦ sup univ fun b' ↦ (f b b').natAbs) =
      sup univ fun b ↦ sup univ fun b' ↦ ((f b b').natAbs : NNReal) := by
    rw [comp_sup_eq_sup_comp ((↑) : ℕ → NNReal)]
    · congr
      ext a
      congr
      simp only [Function.comp_apply]
      rw [comp_sup_eq_sup_comp ((↑) : ℕ → NNReal)]
      · rfl
      · intro x y
        exact Monotone.map_sup (fun a b h ↦ by simp [h]) x y
      · simp
    · intro x y
      refine Monotone.map_sup (fun a b h ↦ by simp [h]) x y
    · simp
  rw [this]
  congr
  ext a
  congr
  ext a'
  rw [coe_nnnorm, NNReal.coe_nat_cast, Nat.cast_natAbs, Int.norm_eq_abs]

lemma baz : ∃ (k : ℕ), ‖M‖ = k := bar M
