/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericRows

/-! Simultaneous coefficient specialization for both matrices of an affine pair. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K]

def affinePairSpecialization (M : Matrix n n K[X]) (P : Matrix m n K[X]) :
    MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K)
    (Sum.elim
      (Sum.elim (fun ij => (M ij.1 ij.2).coeff 0) (fun ij => (P ij.1 ij.2).coeff 0))
      (Sum.elim (fun ij => (M ij.1 ij.2).coeff 1) (fun ij => (P ij.1 ij.2).coeff 1)))

@[simp] theorem affinePairSpecialization_C (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (c : K) : affinePairSpecialization M P (MvPolynomial.C c) = c := by
  simp [affinePairSpecialization]

theorem universalAffineSquare_pair_specialization (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) :
    (universalAffineSquare K n m).map (Polynomial.mapRingHom (affinePairSpecialization M P)) = M := by
  calc
    _ = affineMatrixPencil (fun i j => (M i j).coeff 0) (fun i j => (M i j).coeff 1) := by
      funext i j
      simp [universalAffineSquare, affineMatrixPencil, affinePairSpecialization]
    _ = M := affineMatrixPencil_coefficients M hM

theorem universalAffineRows_pair_specialization (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hP : DegreeBound P 1) :
    (universalAffineRows K n m).map (Polynomial.mapRingHom (affinePairSpecialization M P)) = P := by
  calc
    _ = affineMatrixPencil (fun i j => (P i j).coeff 0) (fun i j => (P i j).coeff 1) := by
      funext i j
      simp [universalAffineRows, affineMatrixPencil, affinePairSpecialization]
    _ = P := affineMatrixPencil_coefficients P hP

end FD56
