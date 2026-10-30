/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailData
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.SixOutputTriplePluckerTangent

/-! The concrete frame and the exact integer coefficients of its actual minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
variable {R : Type*} [CommRing R]

def sixOutputThreeColumnTailFrame : Matrix (Fin 6) (Fin 3) R[X] :=
  fun i j => integerPolynomial (sixOutputThreeColumnTailFrameData i j)

def sixOutputThreeColumnTailMinors : Fin 20 → R[X] := sixOutputTriplePluckerMinors sixOutputThreeColumnTailFrame

def sixOutputThreeColumnTailWitness : Matrix (Fin 20) (Fin 20) R[X] :=
  sixOutputTriplePluckerTangent sixOutputThreeColumnTailMinors

private def tripleProduct (a b c : List ℤ) : List ℤ :=
  integerPolynomialMul (integerPolynomialMul a b) c

private def determinantData (G : Matrix (Fin 3) (Fin 3) (List ℤ)) : List ℤ :=
  integerPolynomialAdd
    (integerPolynomialAdd
      (integerPolynomialAdd (tripleProduct (G 0 0) (G 1 1) (G 2 2))
        (tripleProduct (G 0 1) (G 1 2) (G 2 0)))
      (tripleProduct (G 0 2) (G 1 0) (G 2 1)))
    ((integerPolynomialAdd
      (integerPolynomialAdd (tripleProduct (G 0 2) (G 1 1) (G 2 0))
        (tripleProduct (G 0 1) (G 1 0) (G 2 2)))
      (tripleProduct (G 0 0) (G 1 2) (G 2 1))).map (-·))

private def computedMinorData (c : Fin 20) : List ℤ :=
  determinantData (sixOutputThreeColumnTailFrameData.submatrix (sixOutputTriple c) id)

private theorem computed_minor (c : Fin 20) :
    integerPolynomial (K:=R) (computedMinorData c)=sixOutputThreeColumnTailMinors c := by
  simp [computedMinorData,determinantData,tripleProduct,integerPolynomial_add,
    integerPolynomial_mul,integerPolynomial_neg,sixOutputThreeColumnTailMinors,sixOutputTriplePluckerMinors,
    sixOutputThreeColumnTailFrame,Matrix.det_fin_three,Matrix.submatrix_apply]
  ring

private theorem minor_data_correct : ∀ c : Fin 20,
    integerPolynomialTrim (computedMinorData c)=integerPolynomialTrim (sixOutputThreeColumnTailMinorData c) := by
  decide +kernel

theorem sixOutputThreeColumnTailMinors_entry (c : Fin 20) :
    sixOutputThreeColumnTailMinors (R:=R) c=integerPolynomial (sixOutputThreeColumnTailMinorData c) := by
  rw [← computed_minor]
  exact integerPolynomial_eq_of_trim_eq (minor_data_correct c)

end FD56
