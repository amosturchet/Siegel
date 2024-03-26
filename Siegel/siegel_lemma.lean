import Mathlib
set_option maxHeartbeats 10000000

--statement of Siegel's Lemma, version 1 for the the integers
open Matrix Finset
open BigOperators
open Real
open Nat Set

attribute [local instance] Matrix.seminormedAddCommGroup

variable (m n : ℕ) (b: Fin m)(A M : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ )

lemma foo {A : Type*} [Fintype A] (f : A → ℕ) : (sup univ f) = sup univ fun b ↦ (f b : NNReal) :=
  comp_sup_eq_sup_comp_of_is_total _ Nat.mono_cast (by simp)

lemma norm_mat_int ( hA : A ≠ 0 )  : ∃ (a : ℕ ), ‖A‖=↑a ∧ 1 ≤  a := by

   use sup univ fun b ↦ sup univ fun b' ↦ (A b b').natAbs
   constructor
   -- proof of norm is integer
   ·  simp_rw [norm_def,Pi.norm_def,Pi.nnnorm_def,←NNReal.coe_nat_cast, NNReal.coe_inj, foo]
      congr; ext; congr; ext
      simp only [coe_nnnorm, Int.norm_eq_abs, Int.cast_abs, NNReal.coe_nat_cast, cast_natAbs]
   -- proof of 1 ≤ x
   ·  simp only [bot_eq_zero', gt_iff_lt, zero_lt_one, Finset.le_sup_iff, Finset.mem_univ,
     true_and]
      by_contra h
      push_neg at h
      simp only [lt_one_iff, Int.natAbs_eq_zero] at h
      apply hA
      ext i₀ j₀
      exact h i₀ j₀

lemma mulVec_def : A *ᵥ v = fun x => (fun j => A x j) ⬝ᵥ v := by rfl
lemma dotProd_def : (fun j => A i j) ⬝ᵥ v = ∑ x : Fin n, A i x * v x := by rfl


theorem siegelsLemma  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) : ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ ‖t‖ ≤ ((n*‖A‖)^((m : ℝ )/(n-m))) := by

   rcases norm_mat_int _ _ A hA with ⟨ a, ha⟩
   --Some definitions and relative properties
   let e : ℝ := ↑m / (↑n - ↑m) --exponent
   have hePos : 0 < e := by exact div_pos (cast_pos.mpr hm)  (sub_pos_of_lt (cast_lt.mpr hn))
   let B:= Nat.floor ((n*‖A‖)^e)
   -- B' is the vector with all components = B
   let B':= fun _ : Fin n => (B: ℤ )
   -- T is the box [0 B]^n
   let T:= Finset.Icc 0 B'
   let P := fun i : Fin m => ( ∑  j : Fin n , B * posPart (A i j ))
   let N := fun i : Fin m =>  ( ∑  j : Fin n , B * ( -negPart (A i j )))
   -- S is the box where the image of T goes
   let S:= Finset.Icc (N) (P)

   --In order to apply Pigeohole we need:  ∀ v ∈  T, (A.mulVec v) ∈  S and S.card < T.card

   have him : ∀ v ∈  T, (A.mulVec v) ∈  S := by
      intro v hv
      rw [Finset.mem_Icc] at hv
      rw [Finset.mem_Icc]
      rw [mulVec_def] --unfolds def of MulVec
      refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ --this gives 2 goals
      all_goals simp only [P,N]
      all_goals rw [dotProd_def] -- puts constant inside sum and unfolds def of MulVec
      all_goals gcongr (∑ i_1 : Fin n,?_) with j hj -- gets rid of sums
      all_goals by_cases hsign : 0 ≤ A i j   --we have to distinguish cases: we have now 4 goals
      all_goals rw [<-mul_comm (v j)] --put v j on the left
      ·  rw [negPart_eq_zero.2 hsign]
         simp only [neg_zero, mul_zero]
         exact mul_nonneg (hv.1 j) hsign
      ·  simp only [not_le] at hsign
         rw [negPart_eq_neg.2 (le_of_lt hsign)]
         simp only [neg_neg]
         exact mul_le_mul_of_nonpos_right (hv.2 j) (le_of_lt hsign)
      ·  rw [posPart_eq_self.2  hsign]
         exact mul_le_mul_of_nonneg_right (hv.2 j) hsign
      ·  simp only [not_le] at hsign
         rw [posPart_eq_zero.2 (le_of_lt hsign)]
         simp only [mul_zero]
         exact mul_nonpos_of_nonneg_of_nonpos (hv.1 j) (le_of_lt hsign)

   have hone_le_n_a : 1 ≤ n * a := by exact one_le_mul (one_le_of_lt hn) ha.2

   have hineq1 : 1 ≤  (n*‖A‖)^e:= by
      rw [ha.1]
      apply one_le_rpow _ (le_of_lt hePos)
      exact_mod_cast hone_le_n_a

   have hcardT : T.card=(B+1)^n := by
      rw [Pi.card_Icc 0 B']
      simp only [B',Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_ofNat_add_one, Finset.prod_const,
        Finset.card_fin]

   have hineq2 : ∀ j : Fin m, N j ≤ P j + 1 := by    --needed for hcardS and also later
      intro j
      calc N j ≤ 0 := by
            --apply (mul_nonpos_of_nonneg_of_nonpos (by simp only [cast_nonneg]))
            apply Finset.sum_nonpos
            intro i _
            simp only [mul_neg, Left.neg_nonpos_iff]
            exact mul_nonneg (cast_nonneg B) (negPart_nonneg _)
         _ ≤ P j := by
            --apply mul_nonneg (by simp only [cast_nonneg])
            apply Finset.sum_nonneg
            intro i _
            exact mul_nonneg (cast_nonneg B) (posPart_nonneg _)
         _ ≤ P j + 1 := by exact Int.le_add_one (le_refl P j)


   have hcardS : S.card = (∏ i : Fin m,  (P i - N i + 1)):= by
      rw [Pi.card_Icc (N) (P), Nat.cast_prod]
      congr
      ext j
      rw [Int.card_Icc_of_le _ _ (hineq2 j)]
      ring

   let C:=n*a*B+1

   have hcompexp : (e * (n - m) )= m := by
      simp only [e]
      apply div_mul_cancel₀
      apply sub_ne_zero_of_ne
      norm_cast
      linarith [hn]

   have hcardineq : S.card<T.card := by
      zify
      rw [hcardT, hcardS]
      calc (∏ i : Fin m, (P i - N i + 1)) ≤ (C)^m := by   --recall C:=n*a*B+1
            rw [<-Fin.prod_const m (C : ℤ)]
            apply Finset.prod_le_prod
            all_goals intro i hi
            linarith [hineq2 i]
            simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, cast_succ, cast_mul,
              add_le_add_iff_right, P, N]
            rw [(mul_sum Finset.univ (fun i_1 => (A i i_1)⁺) ↑B).symm, (mul_sum Finset.univ (fun i_1 => (A i i_1)⁻) ↑B).symm]
            rw [←mul_add, mul_comm _ (B : ℤ)]
            apply mul_le_mul_of_nonneg_left _ (by simp only [cast_nonneg])
            rw [←Finset.sum_add_distrib]
            calc ∑ x : Fin n, ((A i x)⁺ + (A i x)⁻) ≤ ∑ x : Fin n, |A i x| := by
                  gcongr with j _
                  rw [posPart_add_negPart (A i j)]
               _ ≤ ∑ x : Fin n, ↑a := by
                  gcongr with j _
                  have h2 :  |A i j| ≤ (a : ℝ ) := by
                     rw [←Int.norm_eq_abs, ←ha.1]
                     exact norm_entry_le_entrywise_sup_norm A
                  exact Int.cast_le.1 h2
               _ = ↑n * ↑a := by simp only [sum_const, card_fin, nsmul_eq_mul]
         _  ≤ ↑(n*a*B + n*a)^m := by
            apply pow_le_pow_left (Int.ofNat_nonneg C)
            simp only [cast_add, cast_mul, cast_one, add_le_add_iff_left, C, B]
            norm_cast
         _ = (n * a * (B + 1)) ^ m := by rfl
         _ = (n * a)^m * (B + 1) ^ m  := by exact mul_pow (↑n * (a:ℤ )) ((B: ℤ)  + 1) m
         _ < (B + 1) ^ (n - m) * (B + 1) ^ m := by
            norm_cast
            rw [mul_lt_mul_right]
            ·  convert_to (n  * (a : ℝ))^m < (B + 1) ^ (n - m)    --pass to real base
               ·  norm_cast
               convert_to (n  * (a : ℝ))^(m : ℝ) < ((B + 1): ℝ) ^ ((n : ℝ) - m) -- pass to real exponents. Non obvious as (n : ℝ) - m = n - m needs m < n
               ·  norm_cast
               ·  rw [<-rpow_nat_cast ((↑B + 1)) (n-m)]
                  congr
                  exact Mathlib.Tactic.Zify.Nat.cast_sub_of_lt hn
               convert_to ((n * a) ^ (m/((n : ℝ)-m)))^ ((n : ℝ)-m)  <((B + 1): ℝ) ^ ((n : ℝ) - m)
               ·  rw [<-rpow_mul _ (m / (n - m)) (n-m),hcompexp]
                  exact_mod_cast Nat.zero_le (n * a)
               apply Real.rpow_lt_rpow --this creates 3 goals: 0 ≤ (↑n * ↑a) ^ (↑m / (↑n - ↑m)), (↑n * ↑a) ^ (↑m / (↑n - ↑m)) < ↑B + 1 and 0 < ↑n - ↑m
               ·  apply rpow_nonneg
                  exact_mod_cast Nat.zero_le (n * a)
               ·  rw [<-ha.1]
                  simp only [B,cast_add, cast_one]
                  exact lt_floor_add_one ((↑n * ‖A‖) ^ (m / ( (n : ℝ ) - ↑m)))
               ·  simp only [sub_pos, cast_lt]
                  exact hn
            ·  rw [pow_pos_iff (Nat.pos_iff_ne_zero.mp hm)]
               exact succ_pos B
         _  = ↑((B + 1) ^ n) := by
            rw [mul_comm,pow_mul_pow_sub]
            norm_cast
            exact (le_of_lt hn)

   --Pigeonhole
   rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardineq him with ⟨ x, hxT,y, hyT ,hneq, hfeq⟩
   use x-y
   -- proof that x - y ≠ 0
   refine ⟨sub_ne_zero.mpr hneq, ?_, ?_⟩
   -- x-y is a solution
   rw [← sub_eq_zero] at hfeq
   rw [sub_eq_add_neg,A.mulVec_add, A.mulVec_neg]
   exact hfeq
   ---Inequality
   rw [<-Matrix.norm_col,norm_le_iff (le_trans zero_le_one hineq1)]
   intro i j
   rw [Finset.mem_Icc] at hyT
   rw [Finset.mem_Icc] at hxT
   simp only [col_apply, Pi.sub_apply, ge_iff_le]
   rw [Int.norm_eq_abs]
   calc ↑|x i - y i| ≤ ((B' i) : ℝ ) := by
         --simp only [Int.cast_abs, Int.cast_sub]
         norm_cast
         rw [abs_le]
         constructor
         ·  simp only [neg_le_sub_iff_le_add]
            apply le_trans (hyT.2 i) _
            simp only [le_add_iff_nonneg_left]
            exact hxT.1 i
         ·  apply le_trans _ (hxT.2 i)
            simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
            exact hyT.1 i
      _ ≤  (↑n * ‖A‖) ^ e := by
         apply le_trans' (Nat.floor_le (le_trans zero_le_one hineq1))
         simp only [B',Int.cast_ofNat, le_refl]
