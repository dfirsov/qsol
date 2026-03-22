import Qsol.Basic
import Quantumlib          -- everything
import Quantumlib.Data.Gate.Basic   -- just gates (Hadamard, CNOT, …)
import Quantumlib.Data.Gate.Pauli  -- Pauli operators + [P| ... ] notation

import Quantumlib.Data.Basic
import Quantumlib.Tactic.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Kron Matrix Complex


lemma exercise_2_1_1 :
   let A := !![5+13*I;
               6+2*I;
               0.53 - 6*I;
               12];
   let B := !![7-8*I;
               4*I;
               2;
               9.4 + 3*I];
   A + B = !![12+5*I;
              6+6*I;
              2.53 - 6*I;
              21.4 + 3*I] := by
   solve_matrix


lemma exercise_2_1_2 :
  ∀ (V W X : CVector n),
    (V + W) + X = V + (W + X) := by
   intros V W X
   ext
   simp only [add_apply]
   rw [add_assoc]

#norm_num ((16 + 2.3*I)* (8 - 2*I)).im

lemma exercise_2_1_3 :
  let c := 8 - 2*I;
  let V := !![16 + 2.3*I;
               -7*I;
               6;
               5-4*I;];
   c • V = !![663/5 - 68/5*I;
             -14 - 56*I;
             48 - 12*I;
             32 - 42*I] := by
   solve_matrix
   refine Complex.ext_iff.mpr ?_
   constructor
   norm_num
   norm_num
   refine Complex.ext_iff.mpr ?_
   constructor <;> norm_num
   refine Complex.ext_iff.mpr ?_
   constructor <;> norm_num

lemma exercise_2_1_4 :
  ∀ (c₁ c₂ : ℂ) (V : CVector n),
    (c₁ + c₂) • V = c₁ • V + c₂ • V := by
   intros c₁ c₂ V
   ext
   simp only [smul_apply, add_apply]
   rw [add_smul]


lemma exercise_2_2_1 :
   let r₁ := 2;
   let r₂ := 3;
   let V := !![2;
              -4;
               1;];
   (r₁ * r₂) • V = (r₁ • (r₂ • V)) := by
   solve_matrix


-- Show which SMul instance is synthesized, then #print the result name:
#synth SMul ℂ ℂ
#check (2 : ℂ) • (1 : ℂ)
#synth Inhabited Nat
set_option pp.all true in #check (· • · : ℂ → ℂ → ℂ)
set_option pp.all true in #check (· • · : ℂ → CMatrix 2 2 → CMatrix 2 2)

lemma exercise_2_2_3_v :
   ∀  (V : CMatrix n m),
      (1 : ℂ) • V = V := by
    intros V
    ext i j
    simp only [smul_apply]
    rw [smul_eq_mul (1 : ℂ) (V i j)]
    simp

lemma exercise_2_2_3_vi :
   ∀ (c₁ c₂ : ℂ) (V : CMatrix n m),
      c₁ • (c₂ • V) = (c₁ * c₂) • V := by
    intros c₁ c₂ V
    ext
    simp only [smul_apply]
    simp
    ring


lemma exercise_2_2_3_viii :
   ∀ (c₁ c₂ : ℂ) (V : CMatrix n m),
      (c₁ + c₂) • V = c₁ • V + c₂ • V := by
    intros c₁ c₂ V
    ext
    simp only [smul_apply, add_apply]
    rw [add_smul]

lemma exercise_2_2_5 :
   let A := !![6-3*I, 2+12*I, -19*I;
               0, 5+2.1*I, 17;
               1, 2+5*I, 3-4.5*I];
   Aᵀ = !![6-3*I, 0, 1;
               2+12*I, 5+2.1*I, 2+5*I;
               -19*I, 17, 3-4.5*I] ∧
   (A.map star) =
            !![6+3*I, 2-12*I, 19*I;
               0, 5-2.1*I, 17;
               1, 2-5*I, 3+4.5*I]  := by
   constructor
   solve_matrix
   solve_matrix
   · simp only [starRingEnd_apply]
     norm_num
   · simp only [starRingEnd_apply]
     norm_num
     ring_nf
   · simp only [starRingEnd_apply]
     norm_num
   · simp only [starRingEnd_apply]
     norm_num
     ring_nf
   · simp only [starRingEnd_apply]
     norm_num
   · simp only [starRingEnd_apply]
     norm_num
     ring_nf
   · simp only [starRingEnd_apply]
     norm_num


lemma exercise_2_2_6 :
 ∀ (c : ℂ) (A : CMatrix m n),
   (c • A)ᴴ  = (star c) • Aᴴ := by
   intros c A
   ext i j
   simp only [smul_apply]
   rw[conjTranspose_smul]
   rw[conjTranspose_apply]
   rw [smul_apply]
   rw [conjTranspose_apply]

-- Adjoint is idempotent: ( A† )† = A.
lemma exercise_2_2_7_vii :
  ∀ (A : CMatrix m n),
    (Aᴴ)ᴴ = A := by
   intros A
   ext i j
   rw[conjTranspose_apply]
   rw[conjTranspose_apply]
   refine Complex.ext_iff.mpr ?_
   constructor
   simp only [star_def]
   simp only [conj_re]
   simp only [star_def]
   simp only [conj_im]
   simp


lemma exercise_2_2_7_viii :
  ∀ (A B : CMatrix m n),
    (A + B)ᴴ = Aᴴ + Bᴴ := by
   intros A B
   ext i j
   rw[conjTranspose_apply]
   simp only [add_apply]
   rw [star_add]
   rw [conjTranspose_apply]
   rw [conjTranspose_apply]

lemma exercise_2_2_7_ix :
  ∀ (c : ℂ) (A : CMatrix m n),
    (c • A)ᴴ = (star c) • Aᴴ := by
   intros c A
   ext i j
   rw[conjTranspose_apply]
   rw[smul_apply]
   rw [star_smul]
   rw[smul_apply]
   rw[conjTranspose_apply]


lemma exercise_2_7_1 :
 !![8,12,6,12,18,9] = !![2,3] ⊗ !![4,6,3] := by
   solve_matrix




lemma exercise_2_7_2: ∀ x : CMatrix 1 3, ∀ y : CMatrix 1 2,
  !![5,6,3,2,0,1] = x ⊗ y -> false := by
  intros x y prf
  have xa1 :  (x ⊗ y) 0 0 = (x 0 0) * (y 0 0) := by
    aesop
  have xa2 :  (x 0 0) * (y 0 0) = 5 := by
    rw [←xa1, ←prf]
    aesop
  have zb1 :  (x ⊗ y) 0 5 = (x 0 2) * (y 0 1) := by
     aesop
  have zb2 :  (x 0 2) * (y 0 1) = 1 := by
     rw [←zb1, ←prf]
     aesop
  have za : (x ⊗ y) 0 4 = 0 := by
     rw [←prf]
     aesop
  have za2 : (x ⊗ y) 0 4 = (x 0 2) * (y 0 0) := by
     aesop
  have za3 : (x 0 2) = 0 ∨ (y 0 0) = 0 := by
     aesop
  aesop

/-- The index swap relating `A ⊗ B` to `B ⊗ A`: swapping the row (column) index pair
exchanges `divNat` and `modNat`, and the entries are equal up to `mul_comm`. -/
theorem kron_comm_apply (A : CMatrix l m) (B : CMatrix n p)
    (i : Fin (l * n)) (j : Fin (m * p)) :
    (A ⊗ B) i j =
      (B ⊗ A) (finProdFinEquiv (i.modNat, i.divNat)) (finProdFinEquiv (j.modNat, j.divNat)) := by
  simp only [kron_apply]
  have key : ∀ {a b : ℕ} (x : Fin a) (y : Fin b),
      (finProdFinEquiv (x, y) : Fin (a * b)).divNat = x ∧
      (finProdFinEquiv (x, y) : Fin (a * b)).modNat = y := fun x y => by
    have h := finProdFinEquiv.symm_apply_apply (x, y)
    simp only [finProdFinEquiv_symm_apply] at h
    exact Prod.mk.inj h
  obtain ⟨h1, h2⟩ := key i.modNat i.divNat
  obtain ⟨h3, h4⟩ := key j.modNat j.divNat
  rw [h1, h2, h3, h4, mul_comm]



theorem exercise_2_7_4 (A : CMatrix l m) (B : CMatrix n p)
    (i : Fin (l * n)) (j : Fin (m * p)) :
    (A ⊗ B) i j =
      (B ⊗ A) (finProdFinEquiv (i.modNat, i.divNat)) (finProdFinEquiv (j.modNat, j.divNat)) := by
  exact (kron_comm_apply A B i j)


lemma exercise_2_7_5 :
   let A := !![1, 2;
               0, 1];
   let B := !![3, 2;
              -1, 0];
   let C := !![6, 5;
               3, 2];
   A ⊗ (B ⊗ C) = (A ⊗ B) ⊗ C := by
   solve_matrix

theorem mod_mul_left_div_self2 (m n k : Nat) : (m % (k * n)) / n = (m / n) % k := by
  rw [Nat.mul_comm k n]
  rw [Nat.mod_mul_right_div_self]

lemma exercise_2_7_6 :
   ∀ A : CMatrix l m,
   ∀ B : CMatrix n p,
   ∀ C : CMatrix q r,
   reindex (finCongr (Nat.mul_assoc l n q)) (finCongr (Nat.mul_assoc m p r)) (A ⊗ B ⊗ C) =
   (A ⊗ (B ⊗ C)) := by
   intros A B C
   ext i j
   simp
   have Ai : ∀ (eq : l * (n * q) = l * n * q), (Fin.cast eq i).divNat.divNat = i.divNat := by
      intro eq
      ext
      simp [Fin.divNat]
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm q n]
   rw [mul_assoc]
   rw [Ai]

   have Aj :  ∀ (eq : (m * (p * r)) = m * p * r), (Fin.cast eq j).divNat.divNat = j.divNat := by
      intro eq
      ext
      simp [Fin.divNat]
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm r p]
   rw [Aj]

   have Bi : ∀ (eq : l * (n * q) = l * n * q), (Fin.cast eq i).divNat.modNat = i.modNat.divNat := by
      intro eq
      ext
      simp [Fin.divNat, Fin.modNat]
      exact Eq.symm (Nat.mod_mul_left_div_self (↑i) q n)
   rw [Bi]

   have Bj :  ∀ (eq : (m * (p * r)) = m * p * r), (Fin.cast eq j).divNat.modNat = j.modNat.divNat := by
      intro eq
      ext
      simp [Fin.divNat, Fin.modNat]
      exact Eq.symm (Nat.mod_mul_left_div_self (↑j) r p)
   rw [Bj]

   have Ci : ∀ (eq : l * (n * q) = l * n * q), (Fin.cast eq i).modNat = i.modNat.modNat := by
      intro eq
      ext
      simp[Fin.modNat]
   rw[Ci]

   have Cj : ∀ (eq : (m * (p * r)) = m * p * r), (Fin.cast eq j).modNat = j.modNat.modNat := by
      intro eq
      ext
      simp[Fin.modNat]
   rw[Cj]

lemma exercise_2_7_7 :
   let A := !![2,3];
   let B := !![1, 2;
               3, 4];
   let C := !![5, 6;
               7, 8]ᴴ ;
   (A ⊗ B)ᴴ  = (Aᴴ ⊗ Bᴴ) := by
   solve_matrix

lemma exercise_2_7_8 : ∀ (A : CMatrix m n) (B : CMatrix p q),
   (A ⊗ B)ᴴ  = (Aᴴ ⊗ Bᴴ) := by
 intros A B
 ext i j
 simp only [conjTranspose]
 simp only [transpose]
 simp_rw [map]
 simp only [kron]
 repeat rw [of_apply]
 rw [@star_mul']



lemma exercise_2_7_9 : ∀ (A : CMatrix m n) (B : CMatrix p q)
   (V: CMatrix n a) (W : CMatrix q b),
   (A ⊗ B) * (V ⊗ W) = (A * V) ⊗ (B * W) := by
   intros A B V W
   ext i j
   simp only [kron, mul_apply]
   rw [of_apply]
   rw [@Fintype.sum_mul_sum]
   simp
   rw [←Equiv.sum_comp (e := finProdFinEquiv)]
   rw [←Finset.univ_product_univ, Finset.sum_product]
   rw [← @Finset.sum_product']
   rw [← @Finset.sum_product']
   rw [@Finset.univ_product_univ]
   congr
   ext x
   have xxx : (finProdFinEquiv (x.1, x.2)).divNat = x.1 := by
    have h := finProdFinEquiv.symm_apply_apply (x.1, x.2)
    simp only [finProdFinEquiv_symm_apply] at h
    aesop
   rw [xxx]
   have yyy : (finProdFinEquiv (x.1, x.2)).modNat = x.2 := by
    have h := finProdFinEquiv.symm_apply_apply (x.1, x.2)
    simp only [finProdFinEquiv_symm_apply] at h
    aesop
   rw [yyy]
   clear xxx yyy
   exact mul_mul_mul_comm (A i.divNat x.1) (B i.modNat x.2) (V x.1 j.divNat) (W x.2 j.modNat)
