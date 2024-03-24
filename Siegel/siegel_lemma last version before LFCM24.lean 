import Mathlib
set_option maxHeartbeats 1000000

--statement of Siegel's Lemma, version 1 for the the integers
open Matrix
open BigOperators
open Real
open Nat Set

--attribute [local instance] Matrix.linftyOpNormedAddCommGroup
--questa norma che ci aveva suggerito Riccardo non va bene perchè è
-- $|A|_\infty = \operatorname{sup}i (\sum_j |A{ij}|)$


--questa qui sotto è quella giusta
attribute [local instance] Matrix.seminormedAddCommGroup

variable (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ )


lemma norm_mat_int ( hA : A ≠ 0 )  : ∃ (a : ℕ ), ‖A‖=↑a ∧ 1 ≤  a := by
   let maxr :=fun i =>( Finset.sup Finset.univ (fun j => Int.natAbs (A i j)))  -- maxr i = max_j |A i j|   max of abs val of entries of i-th row
   let x:= (Finset.sup Finset.univ fun i =>(maxr i ))       -- x = max_i maxr_ i
   use x
   constructor   --split goals: 1: ‖A‖ = ↑x, 2: 1 ≤ x
   apply LE.le.antisymm   -- equality becomes two inequalities
   --proof of ‖A‖ ≤ ↑x
   rw [Matrix.norm_le_iff (cast_nonneg x)]
   intro i₀ j₀
   rw [Int.norm_eq_abs,Int.abs_eq_natAbs]
   norm_cast
   -- have: Int.natAbs (A i₀ j₀) ≤ maxr i₀ := by exact Finset.le_sup (Finset.mem_univ j₀) why doesn't this work?
   let f:= fun (k : Fin n) => Int.natAbs (A i₀ k)
   calc Int.natAbs (A i₀ j₀) = f j₀ := by exact rfl
      _≤ maxr i₀ := by exact Finset.le_sup (Finset.mem_univ j₀)
      _≤ x := by exact Finset.le_sup (Finset.mem_univ i₀)
   -- proof of ↑x ≤ ‖A‖
   calc ↑x  ≤ ((Nat.floor (‖A‖)) : ℝ ) := by
         norm_cast
         apply Finset.sup_le
         intro i₀ hi
         apply Finset.sup_le
         intro j₀ hj
         apply Nat.le_floor
         rw [Nat.cast_natAbs, <-Int.norm_eq_abs]
         exact norm_entry_le_entrywise_sup_norm A
      _ ≤ ‖A‖ := by apply Nat.floor_le (norm_nonneg A)
   -- proof of 1 ≤ x
   by_contra h
   apply hA
   convert_to ∀ (i₀ : Fin m) (j₀ : Fin n), A i₀ j₀=0
   exact Iff.symm ext_iff
   intro i₀ j₀
   push_neg at h
   rw [<-Int.natAbs_eq_zero,<-Nat.le_zero]
   let f:= fun (k : Fin n) => Int.natAbs (A i₀ k)
   calc Int.natAbs (A i₀ j₀) = f j₀ := by exact rfl
      _ ≤ maxr i₀ := by exact Finset.le_sup (Finset.mem_univ j₀)
      _  ≤x := by exact Finset.le_sup (Finset.mem_univ i₀)
      _  ≤ 0 := by exact lt_succ.mp h



theorem siegelsLemma  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) : ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ ‖t‖ ≤ ((n*‖A‖)^((m : ℝ )/(n-m))) := by

   rcases norm_mat_int _ _ A hA with ⟨ a, ha⟩
   --Some definitions and relative properties
   let e : ℝ := ↑m / (↑n - ↑m) --exponent
   have hePos : 0 < e := by exact div_pos (cast_pos.mpr hm)  (sub_pos_of_lt (cast_lt.mpr hn))
   let B:= Nat.floor ((n*‖A‖)^e)
   -- B' is the vector with all components = B
   let B':= fun j : Fin n => (B: ℤ )
   -- T is the box [0 B]^n
   let T:= Finset.Icc 0 B'
   let P := fun i : Fin m => B * ( ∑  j : Fin n , Int.toNat (A i j ) : ℤ   )
   let N := fun i : Fin m => B * ( ∑  j : Fin n , - Int.toNat ( - A i j ) : ℤ  )
   -- S is the box where the image of T goes
   let S:= Finset.Icc (N) (P)

   --In order to apply Pigeohole we need:  ∀ v ∈  T, (A.mulVec v) ∈  S and S.card < T.card

   have him : ∀ v ∈  T, (A.mulVec v) ∈  S := by  --provare a semplificare
      intro v hv
      rw [Finset.mem_Icc] at hv
      rw [Finset.mem_Icc]
      unfold Matrix.mulVec
      -- unfold dotProduct
      simp only [Finset.sum_neg_distrib, mul_neg]
      constructor
      all_goals intro i
      all_goals simp only
      rw [<-neg_mul]
      all_goals rw [Finset.mul_sum]
      all_goals apply Finset.sum_le_sum
      all_goals intro j hj
      all_goals by_cases hsign : 0 ≤ A i j   --we have to distinguish cases
      any_goals simp only [not_le] at hsign
      rw [Int.toNat_eq_zero.2 (Int.neg_nonpos_of_nonneg hsign)]
      any_goals try rw [Int.toNat_of_nonneg (by linarith)]
      any_goals try rw [Int.toNat_of_nonneg hsign]
      any_goals try rw [Int.toNat_eq_zero.2 (le_of_lt hsign)]
      any_goals simp only [CharP.cast_eq_zero, mul_zero,mul_neg, neg_mul, neg_neg]
      exact mul_nonneg hsign (hv.1 j)
      any_goals exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hsign) (hv.1 j)
      all_goals rw [<-mul_comm (v j)]
      exact mul_le_mul_of_nonpos_right (hv.2 j) (le_of_lt hsign)
      exact mul_le_mul_of_nonneg_right (hv.2 j) hsign


   have hone_le_n_a : 1 ≤ n * a := by exact one_le_mul (one_le_of_lt hn) ha.2

   have hineq1 : 1 ≤  (n*‖A‖)^e:= by
      rw [ha.1]
      apply one_le_rpow _ (le_of_lt hePos)
      exact_mod_cast hone_le_n_a

   have hcardT : T.card=(B+1)^n := by
      rw [Pi.card_Icc 0 B']
      simp only [Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_ofNat_add_one, Finset.prod_const,
        Finset.card_fin]

   have hineq2 : ∀ j : Fin m, N j ≤ P j + 1 := by    --needed for hcardS
      intro j
      calc N j ≤ 0 := by
            apply (mul_nonpos_of_nonneg_of_nonpos (Int.ofNat_nonneg B))
            apply Finset.sum_nonpos
            intro i hi
            by_cases h : 0 ≤ A j i
            all_goals simp only [Left.neg_nonpos_iff, cast_nonneg]
         _ ≤ P j := by
            apply mul_nonneg (Int.ofNat_nonneg B)
            apply Finset.sum_nonneg
            intro i hi
            by_cases h1 : 0 ≤ (A j i)
            all_goals simp only [cast_nonneg]
         _ ≤ P j + 1 := by exact Int.le_add_one (le_refl P j)


   have hcardS : S.card = (∏ i : Fin m,  (P i - N i + 1)):= by
      rw [Pi.card_Icc (N) (P), Nat.cast_prod]
      congr
      ext j
      rw [Int.card_Icc_of_le _ _ (hineq2 j)]
      ring

   --from here we start computations to prove  hcardineq : S.card < T.card

   let C:=n*a*B+1

   have hineq3 : ∀ i : Fin m, (P i - N i + 1) ≤ C := by
      intro i
      have h : P i - N i + 1 = B * ((∑ j : Fin n, ↑(Int.toNat (A i j))) +  ∑ j : Fin n, ↑(Int.toNat (-A i j))) + 1 := by
         simp only [Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add, add_left_inj]
         rw [<-mul_add]
      rw [h,<-Finset.sum_add_distrib]
      norm_cast
      apply add_le_add_right
      rw [mul_comm _ B]
      apply mul_le_mul (Nat.le_refl B)  _ (Nat.zero_le (∑ x : Fin n, (Int.toNat (A i x) + Int.toNat (-A i x)))) (Nat.zero_le B)
      calc ∑ x : Fin n, (Int.toNat (A i x) + Int.toNat (-A i x)) ≤ ∑ x : Fin n, a := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Int.toNat_add_toNat_neg_eq_natAbs]
            have h : Int.natAbs (A i j) ≤ (a : ℝ ):= by
               rw [<-ha.1,Nat.cast_natAbs,<-Int.norm_eq_abs]
               exact norm_entry_le_entrywise_sup_norm A
            exact Nat.cast_le.1 h
         _ = n * a := by
            simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]

   have hcompexp : (e * (n - m) )= m := by
      apply div_mul_cancel
      apply sub_ne_zero_of_ne
      norm_cast
      linarith [hn]

   have hineq4 : (n * a)^(m) < (B + 1) ^ (n - m) := by
      convert_to (n  * (a : ℝ))^m < (B + 1) ^ (n - m)    --pass to real base
      norm_cast
      convert_to (n  * (a : ℝ))^(m : ℝ) < ((B + 1): ℝ) ^ ((n : ℝ) - m) -- pass to real exponents. Non obvious as (n : ℝ) - m = n - m needs m < n
      norm_cast
      rw [<-rpow_nat_cast ((↑B + 1)) (n-m)]
      congr
      exact Mathlib.Tactic.Zify.Nat.cast_sub_of_lt hn
      have h :   (n  * (a : ℝ))^(m : ℝ) = ((n * a) ^ (m/((n : ℝ)-m)))^ ((n : ℝ)-m) := by
         rw [<-rpow_mul _ (m / (n - m)) (n-m),hcompexp]
         exact_mod_cast Nat.zero_le (n * a)
      rw [h]
      apply Real.rpow_lt_rpow --this creates 3 goals
      apply rpow_nonneg
      exact_mod_cast Nat.zero_le (n * a)
      rw [<-ha.1]
      simp only [cast_add, cast_one]
      exact lt_floor_add_one ((↑n * ‖A‖) ^ (m / ( (n : ℝ ) - ↑m)))
      simp only [sub_pos, cast_lt]
      exact hn

   have hcardineq : S.card<T.card := by
      zify
      rw [hcardT, hcardS]
      calc (∏ i : Fin m, (P i - N i + 1)) ≤ (C)^m := by   --recall C:=n*a*B+1
            rw [<-Fin.prod_const m (C : ℤ)]
            apply Finset.prod_le_prod
            all_goals intro i hi
            linarith [hineq2 i]
            exact hineq3 i
         _  ≤ ↑(n*a*B + n*a)^m := by
            apply pow_le_pow_left (Int.ofNat_nonneg C)
            simp only [cast_add, cast_mul, cast_one, add_le_add_iff_left]
            exact floor_pos.mp hone_le_n_a
         _  < ↑((B + 1) ^ n) := by
            norm_cast
            calc (n * a * B + n * a) ^ m =(n * a * (B + 1)) ^ m := by rfl
               _ = (n * a)^m * (B + 1) ^ m  := by exact Nat.mul_pow (n * a) (B + 1) m
               _ < (B + 1) ^ (n - m) * (B + 1) ^ m := by
                  rw [mul_lt_mul_right]
                  exact hineq4
                  rw [pow_pos_iff hm]
                  exact succ_pos B
               _ = (B + 1) ^ n := by
                  rw [mul_comm,pow_mul_pow_sub]
                  exact (Nat.le_of_lt hn)

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
   push_cast
   rw [abs_le]
   constructor
   calc -(↑n * ‖A‖) ^ e ≤ - B' i := by
         simp only [Int.cast_ofNat, neg_le_neg_iff]
         exact (Nat.floor_le (le_trans zero_le_one hineq1))
      _  ≤ - ↑(y i) := by
         norm_cast
         simp only [neg_le_neg_iff]
         exact hyT.2 i
      _  ≤ ↑(x i) - ↑(y i) := by
         simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, Int.cast_nonneg]
         exact hxT.1 i
   calc ↑(x i) - ↑(y i) ≤ ↑(B' i) := by
         norm_cast
         simp only [tsub_le_iff_right]
         rw [<-add_zero ((x i))]
         exact Int.add_le_add (hxT.2 i) (hyT.1 i)
      _  ≤  (↑n * ‖A‖) ^ e := by
         apply le_trans' (Nat.floor_le (le_trans zero_le_one hineq1))
         simp only [Int.cast_ofNat, le_refl]
