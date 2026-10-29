/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialDerivationImage

/-! Nonzero coordinate scalings from the base field preserve differential rank. -/

noncomputable section
namespace FD56
open Polynomial

variable {K L j : Type*} [Field K] [Field L] [Algebra K L]

private def coordinateScale (c : j → K) : (j → L[X]) →ₗ[L] (j → L[X]) where
  toFun p i := algebraMap K L (c i) • p i
  map_add' p q := by funext i; exact smul_add _ _ _
  map_smul' a p := by
    funext i
    exact smul_comm (algebraMap K L (c i)) a (p i)

private def coordinateScaleEquiv (c : j → K) (hc : ∀ i, c i ≠ 0) :
    (j → L[X]) ≃ₗ[L] (j → L[X]) where
  toLinearMap := coordinateScale c
  invFun := coordinateScale (fun i => (c i)⁻¹)
  left_inv p := by
    funext i
    change algebraMap K L (c i)⁻¹ • (algebraMap K L (c i) • p i) = p i
    rw [smul_smul, ← map_mul, inv_mul_cancel₀ (hc i), map_one, one_smul]
  right_inv p := by
    funext i
    change algebraMap K L (c i) • (algebraMap K L (c i)⁻¹ • p i) = p i
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ (hc i), map_one, one_smul]

theorem polynomial_derivation_coordinate_scaling_rank
    (c : j → K) (hc : ∀ i, c i ≠ 0) (p : j → L[X]) :
    Module.finrank L (LinearMap.range (polynomialDerivationImageMap (K:=K)
      (fun i => C (algebraMap K L (c i)) * p i))) =
    Module.finrank L (LinearMap.range (polynomialDerivationImageMap (K:=K) p)) := by
  let E := coordinateScaleEquiv (L:=L) c hc
  have hmap : polynomialDerivationImageMap (K:=K)
      (fun i => C (algebraMap K L (c i)) * p i) =
      E.toLinearMap.comp (polynomialDerivationImageMap (K:=K) p) := by
    apply LinearMap.ext
    intro D
    funext i
    change polynomialCoefficientDerivation D (C (algebraMap K L (c i)) * p i) =
      algebraMap K L (c i) • polynomialCoefficientDerivation D (p i)
    rw [Derivation.leibniz, polynomialCoefficientDerivation_C,
      Derivation.map_algebraMap, map_zero, smul_zero, add_zero]
    exact (Polynomial.smul_eq_C_mul (algebraMap K L (c i))).symm
  rw [hmap, LinearMap.range_comp]
  exact E.finrank_map_eq _

end FD56
