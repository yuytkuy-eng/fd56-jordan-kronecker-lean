/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityMinorGradient
import FD56.LinearAlgebra.PolynomialDerivationImage
import FD56.LinearAlgebra.AffineKernelDualRank

/-! Affine variations of the generic pair realize the polynomial pairings
with every selected observability gradient simultaneously. -/

noncomputable section
namespace FD56
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Matrix Polynomial
open scoped BigOperators
variable {R K n m j : Type*} [CommRing R] [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
theorem matrixPairTraceFunctional_transpose (u w : SLInput n m → R) :
    matrixPairTraceFunctional (matrixPairEquiv R R n m u).1.transpose
      (matrixPairEquiv R R n m u).2.transpose w=w ⬝ᵥ u := by
  simp only [matrixPairTraceFunctional,matrixPairEquiv,LinearEquiv.coe_mk,
    LinearMap.coe_mk,AddHom.coe_mk,Matrix.transpose_apply,Matrix.trace,Matrix.diag,
    Matrix.mul_apply,dotProduct,Fintype.sum_sum_type,Fintype.sum_prod_type]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _

omit [DecidableEq m] in
private theorem matrixPairTraceFunctional_affine_transpose
    (u v : SLInput n m → R) (w : SLInput n m → R[X]) :
    matrixPairTraceFunctional
      (affineMatrixPencil (matrixPairEquiv R R n m u).1.transpose
        (matrixPairEquiv R R n m v).1.transpose)
      (affineMatrixPencil (matrixPairEquiv R R n m u).2.transpose
        (matrixPairEquiv R R n m v).2.transpose) w=
      w ⬝ᵥ (fun i => C (u i)+X*C (v i)) := by
  have hM : affineMatrixPencil (matrixPairEquiv R R n m u).1.transpose
      (matrixPairEquiv R R n m v).1.transpose=
      (matrixPairEquiv R[X] R[X] n m (fun i => C (u i)+X*C (v i))).1.transpose := rfl
  have hP : affineMatrixPencil (matrixPairEquiv R R n m u).2.transpose
      (matrixPairEquiv R R n m v).2.transpose=
      (matrixPairEquiv R[X] R[X] n m (fun i => C (u i)+X*C (v i))).2.transpose := rfl
  rw [hM,hP]
  exact matrixPairTraceFunctional_transpose (R:=R[X]) (fun i => C (u i)+X*C (v i)) w

theorem generic_minor_derivation_realizes_affine_pairing
    (level : j → n → ℕ) (row : j → n → m)
    (u v : SLInput n m → AffineCoefficientField K (MatrixParameters n m)) :
    ∃ D : Derivation K (AffineCoefficientField K (MatrixParameters n m))
        (AffineCoefficientField K (MatrixParameters n m)),
      ∀ a, polynomialCoefficientDerivation D
          (observabilitySelectedMatrix (genericAffineSquare K n m)
            (genericAffineRows K n m) (level a) (row a)).det=
        observabilityScalarLift (genericAffineSquare K n m) (genericAffineRows K n m)
          (level a) (row a) ⬝ᵥ (fun i => C (u i)+X*C (v i)) := by
  let L := AffineCoefficientField K (MatrixParameters n m)
  let U := matrixPairEquiv L L n m u
  let V := matrixPairEquiv L L n m v
  obtain ⟨D,hD⟩ := generic_observability_minor_affine_variation
    U.1.transpose V.1.transpose U.2.transpose V.2.transpose
  refine ⟨D,?_⟩
  intro a
  exact (hD (level a) (row a)).trans
    (matrixPairTraceFunctional_affine_transpose (R:=L) u v _)

theorem generic_minor_affine_pairing_range_le
    (level : j → n → ℕ) (row : j → n → m) :
    LinearMap.range (affineDualPairMap (fun i a =>
      observabilityScalarLift (genericAffineSquare K n m) (genericAffineRows K n m)
        (level a) (row a) i)) ≤
      LinearMap.range (polynomialDerivationImageMap (K:=K) (fun a =>
        (observabilitySelectedMatrix (genericAffineSquare K n m)
          (genericAffineRows K n m) (level a) (row a)).det)) := by
  rintro y ⟨⟨u,v⟩,rfl⟩
  obtain ⟨D,hD⟩ := generic_minor_derivation_realizes_affine_pairing level row u v
  exact ⟨D,funext hD⟩

end FD56
