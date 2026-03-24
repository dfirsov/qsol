import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex Real

noncomputable def fromPolar (r θ : ℝ) : ℂ := r * exp (θ * I)

noncomputable def toPolar (z : ℂ) : ℝ × ℝ := (‖z‖, Complex.arg z)

-- Direction 1: fromPolar ∘ toPolar = id, holds for all z : ℂ
theorem fromPolar_toPolar (z : ℂ) :
    fromPolar (toPolar z).1 (toPolar z).2 = z := by
  simp only [fromPolar, toPolar]
  exact Complex.norm_mul_exp_arg_mul_I z

-- Direction 2: toPolar ∘ fromPolar = id, requires r > 0 and θ ∈ (-π, π]
theorem toPolar_fromPolar {r : ℝ} {θ : ℝ}
    (hr : 0 < r) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    toPolar (fromPolar r θ) = (r, θ) := by
  simp only [fromPolar, toPolar, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_of_nonneg hr.le,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  · rw [Complex.exp_mul_I]
    exact Complex.arg_mul_cos_add_sin_mul_I hr hθ
