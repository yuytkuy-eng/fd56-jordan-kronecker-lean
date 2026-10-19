/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SLScalarExtension
import FD56.LinearAlgebra.ClearDenominators

/-! Clearing denominators gives a polynomial SL solution with nonzero scalar
correction. This does not bound its degree or assert a polynomial splitting. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem polynomial_sl_scalar_nonzero {K F n m : Type*} [Field K] [Field F]
    [Algebra K[X] F] [IsFractionRing K[X] F]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n)
    (z : MatrixAlgebraSpace F n m)
    (hz : z ∈ fieldSLRadical (M.map (algebraMap K[X] F)) (P.map (algebraMap K[X] F)))
    (hunit : stabilizerResidual (M.map (algebraMap K[X] F))
      (P.map (algebraMap K[X] F)) z = 1) :
    ∃ (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X]),
      c ≠ 0 ∧ SLRadical M P X U ∧ stabilizerResidual M P (X, U) = c • 1 := by
  let φ := algebraMap K[X] F
  let v := (matrixPairEquiv F F n m).symm z
  have hv : ((slEquationMatrix M P i₀).map φ) *ᵥ v = 0 := by
    rw [slEquationMatrix_map]
    apply (slEquationMatrix_field_kernel_iff _ _ i₀ v).mpr
    simpa [v] using hz
  obtain ⟨d, w, hd, hAw, hw⟩ := kernel_clear_denominators (slEquationMatrix M P i₀) v hv
  let z' := matrixPairEquiv K[X] K[X] n m w
  have hp : (z'.1.map φ, z'.2.map φ) = φ d • z := by
    apply Prod.ext
    · funext i j
      exact hw (.inl (i, j))
    · funext i j
      exact hw (.inr (i, j))
  have he : (stabilizerResidual M P z').map φ = φ d • (1 : Matrix n n F) := by
    rw [← stabilizerResidual_map, hp, map_smul, hunit]
  refine ⟨z'.1, z'.2, d, hd, (slEquationMatrix_kernel_iff M P i₀ w).mp hAw, ?_⟩
  funext i j
  apply IsFractionRing.injective K[X] F
  have hh := congrArg (fun A => A i j) he
  simpa [φ, Matrix.smul_apply, Matrix.one_apply, apply_ite] using hh

end FD56
