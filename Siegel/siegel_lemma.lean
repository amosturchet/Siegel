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

lemma non_zero_mat_norm_ge_one ( hA : A ≠ 0 ) : 1 ≤ ‖A‖ := by     --Da eliminare
   have hexnnzentry : ∃  (i₀ : Fin m) (j₀ : Fin n), 1 ≤ A i₀ j₀  ∨ A i₀ j₀ ≤ -1 := by
      by_contra h
      push_neg at h
      apply hA
      convert_to ∀ (i₀ : Fin m) (j₀ : Fin n), A i₀ j₀ = 0
      exact Iff.symm ext_iff
      intro i₀ j₀
      linarith [h i₀ j₀]
   have h : ∃  (i₀ : Fin m) (j₀ : Fin n ) , 1 ≤ ‖(A i₀ j₀)‖ := by
      rcases hexnnzentry with ⟨i₀ , j₀ , h ⟩
      use  i₀
      use  j₀
      rw [Int.norm_eq_abs,Int.cast_abs,le_abs]
      cases h with
      | inl h₁ =>
         left
         exact Int.cast_one_le_of_pos h₁
      | inr h₂ =>
         right
         rw [le_neg]
         apply Int.cast_le_neg_one_of_neg
         exact Int.le_sub_one_iff.mp h₂
   rcases h with ⟨ i₀, j₀, h1⟩
   calc 1 ≤ ‖(A i₀ j₀)‖ := by exact h1
      _ ≤ ‖A‖ := by exact norm_entry_le_entrywise_sup_norm A



lemma norm_mat_int ( hA : A ≠ 0 )  : ∃ (a : ℕ ), ‖A‖=↑a ∧ 1 ≤  a := by

   let maxr :=fun i =>( Finset.sup Finset.univ (fun j => Int.natAbs (A i j)))  -- maxr i = max_j |A i j|   max of abs val of entries of i-th row
   let x:= (Finset.sup Finset.univ fun i =>(maxr i ))       -- x = max_i maxr_ i
   use x
   constructor   --split goals: 1: ‖A‖ = ↑x, 2: 1 ≤ x
   apply LE.le.antisymm   -- equality becomes two inequalities
   --proof of ‖A‖ ≤ ↑x
   rw [Matrix.norm_le_iff (cast_nonneg x)]
   intro i j
   rw [Int.norm_eq_abs,Int.abs_eq_natAbs]
   norm_cast
   let f:= fun (k : Fin n) => Int.natAbs (A i k)
   calc Int.natAbs (A i j) = f j := by exact rfl
      _≤ maxr i := by exact Finset.le_sup (Finset.mem_univ j)
      _≤ x := by exact Finset.le_sup (Finset.mem_univ i)
   -- proof of ↑x ≤ ‖A‖
   calc ↑x  ≤ ((Nat.floor (‖A‖)) : ℝ ) := by
         norm_cast
         apply Finset.sup_le
         intro i hi
         apply Finset.sup_le
         intro j hj
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
   let f₁:= fun (k : Fin n) => Int.natAbs (A i₀ k)
   calc Int.natAbs (A i₀ j₀) = f₁ j₀ := by exact rfl
      _ ≤ maxr i₀ := by exact Finset.le_sup (Finset.mem_univ j₀)
      _  ≤x := by exact Finset.le_sup (Finset.mem_univ i₀)
      _  ≤ 0 := by exact lt_succ.mp h





theorem siegelsLemma  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) : ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ ‖t‖ ≤ ((n*‖A‖)^((m : ℝ )/(n-m))) := by
   --have hnPos : 0 < n := by linarith
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

   --In order to apply Pigeohole we need:  S.card < T.card and  ∀ v ∈  T, (A.mulVec v) ∈  S

   have him : ∀ v ∈  T, (A.mulVec v) ∈  S := by  --provare a semplificare
      intro v hv
      rw [Finset.mem_Icc] at hv
      rw [Finset.mem_Icc]
      unfold Matrix.mulVec
      unfold dotProduct
      simp only [Finset.sum_neg_distrib, mul_neg]
      constructor
      all_goals intro i
      all_goals simp only
      rw [<-neg_mul,Finset.mul_sum]
      any_goals rw [Finset.mul_sum]
      all_goals apply Finset.sum_le_sum
      all_goals intro j hj
      all_goals by_cases hsign : 0 ≤ A i j
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


   have hone_le_n_a : 1 ≤ n* a := by exact one_le_mul (one_le_of_lt hn) ha.2
 ---da qua
   have hone_le_n_A : 1 ≤ ↑n * ‖A‖ := by   --get rid?
      calc 1 ≤ ‖A‖ := by
            exact non_zero_mat_norm_ge_one _ _ _ hA
         _ ≤ ↑n * ‖A‖ := by
            apply le_mul_of_one_le_left
            exact le_trans (zero_le_one) (non_zero_mat_norm_ge_one _ _ _ hA)
            norm_cast
            exact one_le_of_lt hn

   have hineq1' : 1 ≤  (n*‖A‖)^e:= by --alternative to hineq1
      rw [ha.1]
      apply one_le_rpow _ (le_of_lt hePos)
      exact_mod_cast hone_le_n_a

   have hineq1 : 1 ≤  (n*‖A‖)^e:= by   ---needed at the end also
      apply one_le_rpow hone_le_n_A (le_of_lt hePos)

   have hBpos : 0 < B := by
      rw [Nat.floor_pos]
      exact hineq1

   have hcardT : T.card=(B+1)^n := by
      rw [Pi.card_Icc 0 B']
      simp only [Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_ofNat_add_one, Finset.prod_const,
        Finset.card_fin]

   have hineq2 : ∀ j : Fin m, N j ≤ P j + 1 := by
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
   --da qui iniziano i conti pesanti per dimostrare la disuguaglianza di caridalità

   have heq : ↑⌊↑n * ‖A‖ * ↑B⌋₊=↑⌊↑n * ‖A‖⌋₊ * ↑B:= by
      rw [ha.1]
      norm_cast
      rw [Nat.floor_coe,Nat.floor_coe]

   let C:= Nat.floor ((n*‖A‖*B+1))
   have hineq3 : ∀ i : Fin m, (P i - N i + 1) ≤ Nat.floor ((n*‖A‖*B+1)) := by
      intro i
      have h1 : P i - N i + 1 = B * ((∑ j : Fin n, ↑(Int.toNat (A i j))) +  ∑ j : Fin n, ↑(Int.toNat (-A i j))) + 1 := by
         simp only [Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add, add_left_inj]
         rw [<-mul_add]
      rw [Nat.floor_add_one, h1,<-Finset.sum_add_distrib]
      rw [heq, mul_comm _ B,Nat.cast_add,Nat.cast_one,Nat.cast_mul]
      apply add_le_add_right
      apply mul_le_mul
      exact Int.le_refl ↑B
      rw [ha.1]
      norm_cast
      rw [Nat.floor_coe]
      calc ∑ x : Fin n, (Int.toNat (A i x) + Int.toNat (-A i x)) ≤ ∑ x : Fin n, a := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Int.toNat_add_toNat_neg_eq_natAbs]
            have h : Int.natAbs (A i j) ≤ (a : ℝ ):= by
               rw [<-ha.1,Nat.cast_natAbs,<-Int.norm_eq_abs]
               exact norm_entry_le_entrywise_sup_norm A
            exact Nat.cast_le.1 h
         _ = n * a := by simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]

      apply Finset.sum_nonneg
      intro j hj
      norm_cast
      rw [Int.toNat_add_toNat_neg_eq_natAbs]
      exact Nat.zero_le (Int.natAbs (A i j))
      exact Int.ofNat_nonneg B
      rw [ha.1]
      norm_cast
      simp only [_root_.zero_le]


   have hCpos : 0 < C := by
      rw [Nat.floor_pos]
      calc 1 ≤ ↑n  * ‖A‖ := by exact hone_le_n_A
         _ ≤ ↑n  * ‖A‖  * ↑B := by
            apply le_mul_of_one_le_right
            exact le_trans (zero_le_one) (hone_le_n_A)
            norm_cast
         _ ≤ ↑n * ‖A‖ * ↑B + 1 := by simp only [le_add_iff_nonneg_right, zero_le_one]
   have hcompexp : (e * (n - m) )= m := by
      apply div_mul_cancel
      apply sub_ne_zero_of_ne
      norm_cast
      linarith [hn]
   have hineq4 : (↑n * ‖A‖)^(m) < ↑(B + 1) ^ ((n ) - m) := by
      convert_to (↑n  * ‖A‖ )^(m : ℝ ) < ↑(B + 1) ^ ((n : ℝ ) - m)
      rw [rpow_nat_cast (↑n  * ‖A‖) m]
      rw [<-rpow_nat_cast (↑(B + 1)) (n-m)]
      congr
      rw [Nat.cast_sub (le_of_lt hn)]
      calc (↑n  * ‖A‖ )^(m : ℝ ) = ((n*‖A‖)^(m/((n : ℝ)-m)))^ ((n : ℝ)-m) := by
            rw [<-rpow_mul _ (m / (n - m)) (n-m),hcompexp]
            exact le_trans (zero_le_one) (hone_le_n_A)
         _ < ↑(B + 1) ^ ((n : ℝ)-m) :=by
            apply Real.rpow_lt_rpow
            apply rpow_nonneg
            exact le_trans (zero_le_one) (hone_le_n_A)
            simp only [cast_add, cast_one]
            exact lt_floor_add_one ((↑n * ‖A‖) ^ (m / ( (n : ℝ ) - ↑m)))
            simp only [sub_pos, cast_lt]
            exact hn





   have hineq5  : ( ↑((Nat.floor (n*‖A‖*B + n*‖A‖))^m ) : ℝ ) < (↑((B + 1) ^ n)  ) := by
      have h1 : n*‖A‖*B  + n*‖A‖ = n*‖A‖* (B  + 1) := by linarith
      rw [h1]
      have h2 : (↑n * ‖A‖ * (↑B + 1) )^ m < (↑B + 1) ^ n := by
         calc (↑n * ‖A‖ * (↑B + 1) )^ m =(↑n * ‖A‖)^m * (↑B + 1) ^ m := by  rw [mul_pow]
            _ < (↑B + 1) ^ (n-m) * (↑B + 1) ^ m := by
               rw [mul_lt_mul_right]
               push_cast at hineq4
               exact hineq4
               norm_cast
               rw [pow_pos_iff]
               linarith
               exact hm
            _ = (↑B + 1) ^ n := by
               rw [mul_comm, pow_mul_pow_sub]
               exact le_of_lt hn
      push_cast
      apply lt_of_lt_of_le' h2
      apply pow_le_pow_left
      simp only [cast_nonneg]
      apply Nat.floor_le
      calc 0 ≤ ↑n * ‖A‖  := by exact le_trans zero_le_one hone_le_n_A
         _ ≤ ↑n * ‖A‖ * ↑B := by
            apply le_mul_of_one_le_right
            exact le_trans (zero_le_one) (hone_le_n_A)
            norm_cast
         _ ≤ ↑n * ‖A‖ * (↑B + 1 ):= by linarith

   have hcardineq : S.card<T.card := by
      zify
      rw [hcardT, hcardS]
      calc (∏ i : Fin m, (P i - N i + 1)) ≤ (C)^m := by
            convert_to (∏ i : Fin m, (P i - N i + 1)) ≤ (∏ i : Fin m, C : ℤ)
            simp
            apply Finset.prod_le_prod
            intro i hi
            linarith [hineq2 i]
            intro i hi
            exact hineq3 i
         _  ≤ ↑(Nat.floor (n*‖A‖*B + n*‖A‖))^m := by
            apply pow_le_pow_left
            norm_cast
            exact (le_of_lt hCpos)
            norm_cast
            apply Nat.floor_le_floor
            simp
            exact hone_le_n_A
         _  < ↑((B + 1) ^ n) := by
            norm_cast
            exact Nat.cast_lt.1 (hineq5)

   --fine conti



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
