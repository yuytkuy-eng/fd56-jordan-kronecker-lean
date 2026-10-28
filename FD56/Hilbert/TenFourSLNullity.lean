/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenFourSLData
import FD56.Hilbert.TenFourSLObservabilityData
import FD56.Stabilizer.ObservableRadical
import FD56.Stabilizer.FieldSLMatrix
import FD56.LinearAlgebra.RankSpecializationExtension
import Mathlib.FieldTheory.RatFunc.Basic

/-! The full ten-state, four-output SL equation matrix has rational nullity five.
Only the small prefix and terminal observability inverse certificates are used. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K F : Type*} [Field K] [Field F]
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option Elab.async false

theorem tenFour_M_at_zero :
    (tenFourM (K:=K)).map (Polynomial.evalRingHom 0)=tenFourM0 := by
  ext i j
  change (integerPolynomial (tenFourMData i j)).eval 0=tenFourM0 (K:=K) i j
  rw [← Polynomial.coeff_zero_eq_eval_zero,integerPolynomial_coeff]
  have h : ∀ i j, (tenFourMData i j).getD 0 0=tenFourM0Integer i j := by decide
  exact congrArg (fun z : ℤ => (z : K)) (h i j)

theorem tenFour_P_at_zero :
    (tenFourP (K:=K)).map (Polynomial.evalRingHom 0)=tenFourP0 := by
  ext i j
  change (integerPolynomial (tenFourPData i j)).eval 0=tenFourP0 (K:=K) i j
  rw [← Polynomial.coeff_zero_eq_eval_zero,integerPolynomial_coeff]
  have h : ∀ i j, (tenFourPData i j).getD 0 0=tenFourP0Integer i j := by decide
  exact congrArg (fun z : ℤ => (z : K)) (h i j)

theorem tenFour_observability_two_field_surjective
    (φ : K[X] →+* F) (hφ : Function.Injective φ) :
    Function.Surjective (observabilityMatrix ((tenFourM (K:=K)).map φ)
      (tenFourP.map φ) 2).mulVec := by
  have hz : Function.Surjective ((observabilityMatrix (tenFourM (K:=K)) tenFourP 2).map
      (Polynomial.evalRingHom 0)).mulVec := by
    rw [observabilityMatrix_map,tenFour_M_at_zero,tenFour_P_at_zero]
    intro v
    refine ⟨tenFourO2Right*ᵥv,?_⟩
    rw [Matrix.mulVec_mulVec,tenFour_observability_two_right_inverse,Matrix.one_mulVec]
  have h := matrix_surjective_of_field_specialization (Polynomial.evalRingHom (0 : K))
    φ hφ (observabilityMatrix tenFourM tenFourP 2) hz
  simpa only [observabilityMatrix_map] using h

theorem tenFour_observability_three_field_injective
    (φ : K[X] →+* F) (hφ : Function.Injective φ) :
    Function.Injective (observabilityMatrix ((tenFourM (K:=K)).map φ)
      (tenFourP.map φ) 3).mulVec := by
  have hz : Function.Injective ((observabilityMatrix (tenFourM (K:=K)) tenFourP 3).map
      (Polynomial.evalRingHom 0)).mulVec := by
    rw [observabilityMatrix_map,tenFour_M_at_zero,tenFour_P_at_zero]
    intro v w hvw
    have hh := congrArg (fun z => (tenFourO3Left (K:=K))*ᵥz) hvw
    simpa only [Matrix.mulVec_mulVec,tenFour_observability_three_left_inverse,
      Matrix.one_mulVec] using hh
  have h := matrix_injective_of_field_specialization (Polynomial.evalRingHom (0 : K))
    φ hφ (observabilityMatrix tenFourM tenFourP 3) hz
  simpa only [observabilityMatrix_map] using h

theorem tenFour_sl_field_nullity
    (φ : K[X] →+* F) (hφ : Function.Injective φ) (i₀ : Fin 10) :
    Module.finrank F (LinearMap.ker (Matrix.toLin'
      ((slEquationMatrix (tenFourM (K:=K)) tenFourP i₀).map φ)))=5 := by
  let M := (tenFourM (K:=K)).map φ
  let P := (tenFourP (K:=K)).map φ
  have hs : Function.Surjective (observabilityMatrix M P 2).mulVec :=
    tenFour_observability_two_field_surjective φ hφ
  have hi : Function.Injective (observabilityMatrix M P 3).mulVec :=
    tenFour_observability_three_field_injective φ hφ
  have hfirst : Module.finrank F (unobservableSpace M P 2)=2 := by
    have hh := (Matrix.toLin' (observabilityMatrix M P 2)).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs,finrank_top,Module.finrank_fintype_fun_eq_card,
      observabilityMatrix_ker,Module.finrank_fintype_fun_eq_card] at hh
    simp only [Fintype.card_prod,Fintype.card_fin] at hh
    omega
  have hnext : Module.finrank F (unobservableSpace M P 3)=0 := by
    rw [← observabilityMatrix_ker,LinearMap.ker_eq_bot.mpr hi,finrank_bot]
  rw [slEquationMatrix_specialized_finrank]
  exact sl_finrank_of_observability 1 2 M P (by decide) hfirst hnext

theorem tenFour_sl_fraction_nullity (i₀ : Fin 10) :
    Module.finrank (RatFunc K) (LinearMap.ker (Matrix.toLin'
      ((slEquationMatrix (tenFourM (K:=K)) tenFourP i₀).map
        (algebraMap K[X] (RatFunc K)))))=5 :=
  tenFour_sl_field_nullity _ (IsFractionRing.injective _ _) i₀

end FD56
