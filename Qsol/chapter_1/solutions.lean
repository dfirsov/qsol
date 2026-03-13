import Qsol.Basic
import Quantumlib          -- everything
import Quantumlib.Data.Gate.Basic   -- just gates (Hadamard, CNOT, …)
import Quantumlib.Data.Gate.Pauli  -- Pauli operators + [P| ... ] notation

import Quantumlib.Data.Basic
import Quantumlib.Tactic.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Kron Matrix Complex


lemma exercise_1_1_2 : Complex.I ^15 = - Complex.I := by
   rw [Complex.I_pow_eq_pow_mod]
   simp

lemma exercise_1_1_3 :
  let c1 := -3 + Complex.I;
  let c2 := 2 - 4 * Complex.I;
  c1 + c2 = -1 + -3 * Complex.I := by
  intros c1 c2
  norm_num [Complex.ext_iff]
  constructor
  · simp [c1 , c2]
    norm_num
  · simp [c1, c2]
    norm_num


lemma exercise_1_2_5 :
  ∀ (c1 c2 : ℂ),
   ‖c1‖ * ‖c2‖ = ‖c1 * c2‖ := by
   intros c1 c2
   rw [norm_def, norm_def, norm_def, normSq_mul, Real.sqrt_mul (normSq_nonneg _)]

-- normSq_add, Real.sqrt_le
lemma exercise_1_2_6 :
  ∀ (c1 c2 : ℂ),
    ‖c1 + c2‖ ≤ ‖c1‖ + ‖c2‖ := by
   intros c1 c2
   rw [norm_def, norm_def, norm_def]
   rw [normSq_add]
   simp
   refine Real.sqrt_le_iff.mpr ?_
   constructor
   · apply add_nonneg
     exact Real.sqrt_nonneg (normSq c1)
     exact Real.sqrt_nonneg (normSq c2)
   · rw[add_sq]
     rw[Real.sq_sqrt]
     · rw[Real.sq_sqrt]
       · have : (c1.re * c2.re + c1.im * c2.im) ≤ √(normSq c1) * √(normSq c2)
         rw[← Real.sqrt_mul]
         rw[← normSq_mul]
         rw[normSq_apply]
         rw[←sq]
         rw[←sq]
         refine Real.le_sqrt_of_sq_le ?_
         rw[mul_re]
         rw[mul_im]
         rw[add_sq]
         rw[add_sq]
         ring_nf
         simp
         rw [← le_sub_iff_add_le]
         ring_nf
         apply le_of_sub_nonneg
         have : c1.re ^ 2 * c2.im ^ 2 + c2.re ^ 2 * c1.im ^ 2 - c1.re * c2.re * c1.im * c2.im * 2
            = (c1.re * c2.im - c2.re * c1.im) ^ 2 := by
            ring_nf
         rw[this]
         apply sq_nonneg
         exact normSq_nonneg c1
         linarith
       · exact normSq_nonneg c2
     · exact normSq_nonneg c1


lemma exercise_1_2_10 :
  ∀ (c1 c2 : ℂ),
  (star c1) + (star c2) = star (c1 + c2) := by
  intros c1 c2
  simp only [star]
  rw [add_im]
  rw [add_re]
  apply Complex.ext
  · simp [Complex.add_re]
  · simp [Complex.add_im ]
    simp[add_comm]


lemma exercise_1_2_11 :
  ∀ (c1 c2 : ℂ),
  (star c1) * (star c2) = star (c1 * c2) := by
  intros c1 c2
  simp only [star]
  rw [mul_im]
  rw [mul_re]
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im, add_comm]
