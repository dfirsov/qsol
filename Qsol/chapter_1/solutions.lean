import Qsol.Basic
import Quantumlib          -- everything
import Quantumlib.Data.Gate.Basic   -- just gates (Hadamard, CNOT, …)
import Quantumlib.Data.Gate.Pauli  -- Pauli operators + [P| ... ] notation

import Quantumlib.Data.Basic
import Quantumlib.Tactic.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Complex Real

lemma exercise_1_1_1 : ∀ (x : ℝ), x^4 + 2*x^2 + 1 > 0 := by
   have : ∀ (x : ℝ), x^4 + 2*x^2 + 1 = (x^2 + 1)^2 := by
     intro x
     simp [sq, mul_add, mul_comm]
     ring
   intro x
   rw[this]
   apply sq_pos_of_ne_zero
   intro h
   have : x^2 + 1 > 0 := by
      apply add_pos_of_nonneg_of_pos
      exact sq_nonneg x
      exact zero_lt_one
   aesop

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

lemma exercise_1_2_3 :
    (3 * Complex.I : ℂ) / (-1 - Complex.I) = -(3/2) - (3/2) * Complex.I := by
  refine Complex.ext_iff.mpr ?_
  constructor
  · simp [Complex.div_re, normSq_apply]
    norm_num
  · simp [Complex.div_im, normSq_apply]
    norm_num

lemma exercise_1_2_4 :
  let c := 4 - 3 * Complex.I;
  ‖c‖ = 5 := by
  simp [norm_def, normSq_apply]
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


lemma exercise_1_2_8 :
  ∀ (c : ℂ),
  c * 1 = c := by
  intros c
  refine Complex.ext_iff.mpr ?_
  constructor <;> simp



lemma exercise_1_2_9 :
  ∀ (c : ℂ),
  c * -1 = -c.re - c.im * Complex.I := by
  intros c
  refine Complex.ext_iff.mpr ?_
  constructor
  · simp [mul_re]
  · simp [mul_im]

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

lemma exercise_1_3_4 :
  let c1 := -2 - Complex.I;
  let c2 := -1 - 2 * Complex.I;
  let c1c2 := c1 * c2;
  let rho1:= ‖c1‖;
  let rho2 := ‖c2‖;
  let theta1 := Complex.arg c1;
  let theta2 := Complex.arg c2;
  rho1 * rho2 * Complex.exp ((theta1 + theta2) * Complex.I)
  = c1c2 := by
  intros c1 c2 c1c2 rho1 rho2 theta1 theta2
  have h1 : (rho1 : ℂ) * Complex.exp ((theta1 : ℂ) * Complex.I) = c1 :=
    Complex.norm_mul_exp_arg_mul_I c1
  have h2 : (rho2 : ℂ) * Complex.exp ((theta2 : ℂ) * Complex.I) = c2 :=
    Complex.norm_mul_exp_arg_mul_I c2
  have step : (rho1 : ℂ) * rho2 * Complex.exp (((theta1 : ℂ) + theta2) * Complex.I) =
    (↑rho1 * Complex.exp (↑theta1 * Complex.I)) * (↑rho2 * Complex.exp (↑theta2 * Complex.I)) := by
    rw [add_mul, Complex.exp_add]; ring
  rw [step, h1, h2]


lemma exercise_1_3_7 :
    let c1 := 2 + 2 * Complex.I;
    let c2 := 1 -  Complex.I;
  c1 / c2 = 2 * Complex.I := by
  intros c1 c2
  simp[c1, c2]
  refine Complex.ext_iff.mpr ?_
  simp[Complex.div_re]
  constructor
  · ring
  · simp[Complex.div_im]
    ring
    simp[normSq_apply]
    norm_num

lemma eq_1_49 :
 ∀ (c : ℂ),
   c * (star c) = ‖c‖ ^ 2 := by
  intros c
  refine Complex.ext_iff.mpr ?_
  constructor
  · simp [mul_re]
    rw [← mul_conj']
    simp[mul_re]
  · simp [mul_im]
    rw [← mul_conj']
    simp[mul_im]




-- Let c = 1 − i. Convert it to polar coordinates, calculate its fifth
-- power, and revert the answers to Cartesian coordinates.
-- Polar form: c = √2 · exp(-πi/4)
-- Fifth power: c^5 = (√2)^5 · exp(-5πi/4) = 4√2 · exp(-5πi/4)
-- Converting back: exp(-5πi/4) = -√2/2 + (√2/2)i, so c^5 = -4 + 4i
lemma exercise_1_3_8 :
    (1 - Complex.I : ℂ) ^ 5 = -4 + 4 * Complex.I := by
  -- Step 1: express 1 - i in polar form: 1 - i = √2 · exp(-πi/4)
  have hnorm : ‖(1 - Complex.I : ℂ)‖ = Real.sqrt 2 := by
    simp [norm_def, normSq_apply]; norm_num
  -- arg(1 - i) = -π/4  via  arg_of_im_neg: arg z = -arccos(re/‖z‖) when im < 0
  have harg : Complex.arg (1 - Complex.I) = -(Real.pi / 4) := by
    rw [Complex.arg_of_im_neg (by norm_num : (1 - Complex.I : ℂ).im < 0), hnorm]
    simp only [Complex.sub_re, Complex.one_re, Complex.I_re, sub_zero]
    -- arccos(1/√2) = π/4 since cos(π/4) = 1/√2 and π/4 ∈ [0, π]
    have hcos14 : (1 : ℝ) / Real.sqrt 2 = Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      rw [div_eq_div_iff (Real.sqrt_ne_zero'.mpr (by norm_num)) (by norm_num : (2:ℝ) ≠ 0)]
      linarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    have h14 : Real.arccos (1 / Real.sqrt 2) = Real.pi / 4 := by
      rw [hcos14]
      exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    linarith
  have hpolar : (1 - Complex.I : ℂ) =
      ↑(Real.sqrt 2) * Complex.exp (↑(-(Real.pi / 4)) * Complex.I) :=
    calc (1 - Complex.I : ℂ)
        = ↑‖(1 - Complex.I : ℂ)‖ * Complex.exp (↑(Complex.arg (1 - Complex.I)) * Complex.I) :=
          (Complex.norm_mul_exp_arg_mul_I _).symm
      _ = ↑(Real.sqrt 2) * Complex.exp (↑(-(Real.pi / 4)) * Complex.I) := by
          rw [hnorm, harg]
  -- Step 2: raise to the 5th power in polar form: (√2·exp(-πi/4))^5 = (√2)^5 · exp(-5πi/4)
  -- (√2)^5 = 4√2
  have hsqrt5 : (↑(Real.sqrt 2) : ℂ) ^ 5 = ↑(4 * Real.sqrt 2) := by
    norm_cast
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc Real.sqrt 2 ^ 5
        = (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 ^ 2 * Real.sqrt 2 := by rw [h2]
      _ = 4 * Real.sqrt 2 := by norm_num
  -- exp(-πi/4)^5 = exp(-5πi/4)
  have hexp5 : Complex.exp (↑(-(Real.pi / 4)) * Complex.I) ^ 5 =
      Complex.exp (↑(-(5 * Real.pi / 4)) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  -- Step 3: convert exp(-5πi/4) back to Cartesian: cos(-5π/4) = -√2/2, sin(-5π/4) = √2/2
  have hcos : Real.cos (-(5 * Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
    rw [Real.cos_neg, show 5 * Real.pi / 4 = Real.pi + Real.pi / 4 by ring,
        Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]; ring
  have hsin : Real.sin (-(5 * Real.pi / 4)) = Real.sqrt 2 / 2 := by
    rw [Real.sin_neg, show 5 * Real.pi / 4 = Real.pi + Real.pi / 4 by ring,
        Real.sin_add, Real.cos_pi, Real.sin_pi, Real.sin_pi_div_four]; ring
  -- exp(↑r * I).re = cos r  and  exp(↑r * I).im = sin r  (Euler's formula components)
  have hexp_cart : Complex.exp (↑(-(5 * Real.pi / 4)) * Complex.I) =
      ↑(-(Real.sqrt 2 / 2)) + ↑(Real.sqrt 2 / 2) * Complex.I := by
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re, hcos]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
    · rw [Complex.exp_ofReal_mul_I_im, hsin]
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
  -- Assemble: 4√2 · (-√2/2 + √2/2·i) = -4 + 4i
  rw [hpolar, mul_pow, hsqrt5, hexp5, hexp_cart]
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;>
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
  nlinarith [Real.sqrt_nonneg 2]




-- claude --resume aa171c10-b5d7-4179-89fb-9548dd639cc7
-- exercise 1_3_9 find all cube roots of c = 1 + i
-- and prove that they are indeed cube roots of c.
