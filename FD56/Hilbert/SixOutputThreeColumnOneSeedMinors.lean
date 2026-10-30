/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnOneSeedData
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

def sixOutputThreeColumnOneSeedFrame : Matrix (Fin 6) (Fin 3) R[X] :=
  fun i j => integerPolynomial (sixOutputThreeColumnOneSeedFrameData i j)

def sixOutputThreeColumnOneSeedMinors : Fin 20 → R[X] := sixOutputTriplePluckerMinors sixOutputThreeColumnOneSeedFrame

def sixOutputThreeColumnOneSeedWitness : Matrix (Fin 20) (Fin 20) R[X] :=
  sixOutputTriplePluckerTangent sixOutputThreeColumnOneSeedMinors

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
  determinantData (sixOutputThreeColumnOneSeedFrameData.submatrix (sixOutputTriple c) id)

private theorem computed_minor (c : Fin 20) :
    integerPolynomial (K:=R) (computedMinorData c)=sixOutputThreeColumnOneSeedMinors c := by
  simp [computedMinorData,determinantData,tripleProduct,integerPolynomial_add,
    integerPolynomial_mul,integerPolynomial_neg,sixOutputThreeColumnOneSeedMinors,sixOutputTriplePluckerMinors,
    sixOutputThreeColumnOneSeedFrame,Matrix.det_fin_three,Matrix.submatrix_apply]
  ring

private theorem minor_data_correct : ∀ c : Fin 20,
    integerPolynomialTrim (computedMinorData c)=integerPolynomialTrim (sixOutputThreeColumnOneSeedMinorData c) := by
  decide +kernel

theorem sixOutputThreeColumnOneSeedMinors_entry (c : Fin 20) :
    sixOutputThreeColumnOneSeedMinors (R:=R) c=integerPolynomial (sixOutputThreeColumnOneSeedMinorData c) := by
  rw [← computed_minor]
  exact integerPolynomial_eq_of_trim_eq (minor_data_correct c)

end FD56
