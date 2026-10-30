/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PermutedSixOutputThreeTailData
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import FD56.LinearAlgebra.RankSpecializationExtension
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.SixOutputPluckerTangent

/-! An integral frame and the actual fifteen-equation Plucker tangent. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
variable {R : Type*} [CommRing R]

def permutedSixOutputThreeTailU : Fin 6 → R[X] := fun i => integerPolynomial (permutedSixOutputThreeTailUData i)
def permutedSixOutputThreeTailV : Fin 6 → R[X] := fun i => integerPolynomial (permutedSixOutputThreeTailVData i)

def permutedSixOutputThreeTailWitness : Matrix (Fin 15) (Fin 15) R[X] :=
  sixOutputPluckerTangent (twoColumnWedge permutedSixOutputThreeTailU permutedSixOutputThreeTailV)

private def wedgeData (i j : Fin 6) : List ℤ :=
  integerPolynomialAdd (integerPolynomialMul (permutedSixOutputThreeTailUData i) (permutedSixOutputThreeTailVData j))
    ((integerPolynomialMul (permutedSixOutputThreeTailUData j) (permutedSixOutputThreeTailVData i)).map (-·))

def permutedSixOutputThreeTailComputedData : Matrix (Fin 15) (Fin 15) (List ℤ) := fun i j =>
  let q := sixOutputQuad i
  let p := sixOutputPair j
  if p=(q 0,q 1) then wedgeData (q 2) (q 3) else
  if p=(q 0,q 2) then (wedgeData (q 1) (q 3)).map (-·) else
  if p=(q 0,q 3) then wedgeData (q 1) (q 2) else
  if p=(q 1,q 2) then wedgeData (q 0) (q 3) else
  if p=(q 1,q 3) then (wedgeData (q 0) (q 2)).map (-·) else
  if p=(q 2,q 3) then wedgeData (q 0) (q 1) else []

def permutedSixOutputThreeTailPolynomialData : Matrix (Fin 15) (Fin 15) (List ℤ) :=
  ![![[-1,1],[],[0,0,-1,1],[],[],[0,0,0,-1,1],[],[],[],[0,0,0,0,0,1,-1],[],[],[],[],[]],
    ![[0,0,1],[0,0,0,0,1,-1],[],[0,0,-1,1],[],[0,0,0,0,0,1],[],[],[],[],[0,0,0,0,0,1,-1],[],[],[],[]],
    ![[0,1],[0,0,0,1,-1],[],[],[0,0,-1,1],[0,0,0,0,1],[],[],[],[],[],[0,0,0,0,0,1,-1],[],[],[]],
    ![[0,0,1,-1],[],[0,0,0,0,1,-1],[],[],[],[0,0,0,0,0,1],[0,0,0,1,-1],[],[],[],[],[0,0,0,0,0,1,-1],[],[]],
    ![[0,1,-1],[],[0,0,0,1,-1],[],[],[],[0,0,0,0,1],[],[0,0,0,1,-1],[],[],[],[],[0,0,0,0,0,1,-1],[]],
    ![[],[],[],[0,0,0,1,-1],[0,0,0,0,-1,1],[],[],[0,0,0,0,1],[0,0,0,0,0,-1],[],[],[],[],[],[0,0,0,0,0,1,-1]],
    ![[],[0,0,1,-1],[0,0,-1],[-1,1],[],[],[],[],[],[0,0,0,0,0,1],[0,0,0,1,-1],[],[],[],[]],
    ![[],[0,1,-1],[0,-1],[],[-1,1],[],[],[],[],[0,0,0,0,1],[],[0,0,0,1,-1],[],[],[]],
    ![[],[],[],[0,-1],[0,0,1],[],[],[],[],[],[0,0,0,0,1],[0,0,0,0,0,-1],[],[],[]],
    ![[],[],[],[0,-1,1],[0,0,1,-1],[],[],[],[],[],[],[],[0,0,0,0,1],[0,0,0,0,0,-1],[0,0,0,-1,1]],
    ![[],[],[],[],[],[0,0,1,-1],[0,0,-1],[-1,1],[],[0,0,0,0,-1,1],[],[],[0,0,-1,1],[],[]],
    ![[],[],[],[],[],[0,1,-1],[0,-1],[],[-1,1],[0,0,0,-1,1],[],[],[],[0,0,-1,1],[]],
    ![[],[],[],[],[],[],[],[0,-1],[0,0,1],[],[0,0,0,-1,1],[0,0,0,0,1,-1],[],[],[0,0,-1,1]],
    ![[],[],[],[],[],[],[],[0,-1,1],[0,0,1,-1],[],[],[],[0,0,0,-1,1],[0,0,0,0,1,-1],[]],
    ![[],[],[],[],[],[],[],[],[],[],[0,-1,1],[0,0,1,-1],[0,1],[0,0,-1],[-1,1]]]

private theorem permutedSixOutputThreeTail_computed_polynomial (i j : Fin 15) :
    integerPolynomial (K:=R) (permutedSixOutputThreeTailComputedData i j)=permutedSixOutputThreeTailWitness i j := by
  dsimp only [permutedSixOutputThreeTailComputedData,permutedSixOutputThreeTailWitness,sixOutputPluckerTangent]
  split_ifs <;>
    simp [wedgeData,integerPolynomial_add,integerPolynomial_mul,integerPolynomial_neg,
      permutedSixOutputThreeTailU,permutedSixOutputThreeTailV,twoColumnWedge,sub_eq_add_neg]

private theorem polynomial_row0 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 0 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 1 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 2 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 3 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 4 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 4 j) := by decide +kernel

private theorem polynomial_row5 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 5 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 5 j) := by decide +kernel

private theorem polynomial_row6 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 6 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 6 j) := by decide +kernel

private theorem polynomial_row7 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 7 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 7 j) := by decide +kernel

private theorem polynomial_row8 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 8 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 8 j) := by decide +kernel

private theorem polynomial_row9 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 9 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 9 j) := by decide +kernel

private theorem polynomial_row10 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 10 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 10 j) := by decide +kernel

private theorem polynomial_row11 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 11 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 11 j) := by decide +kernel

private theorem polynomial_row12 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 12 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 12 j) := by decide +kernel

private theorem polynomial_row13 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 13 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 13 j) := by decide +kernel

private theorem polynomial_row14 : ∀ j : Fin 15,
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData 14 j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData 14 j) := by decide +kernel

attribute [local irreducible] permutedSixOutputThreeTailComputedData permutedSixOutputThreeTailPolynomialData

private theorem polynomial_data_correct (i j : Fin 15) :
    integerPolynomialTrim (permutedSixOutputThreeTailComputedData i j)=
      integerPolynomialTrim (permutedSixOutputThreeTailPolynomialData i j) := by
  fin_cases i
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j
  · exact polynomial_row5 j
  · exact polynomial_row6 j
  · exact polynomial_row7 j
  · exact polynomial_row8 j
  · exact polynomial_row9 j
  · exact polynomial_row10 j
  · exact polynomial_row11 j
  · exact polynomial_row12 j
  · exact polynomial_row13 j
  · exact polynomial_row14 j

theorem permutedSixOutputThreeTailWitness_entry (i j : Fin 15) :
    permutedSixOutputThreeTailWitness (R:=R) i j=integerPolynomial (permutedSixOutputThreeTailPolynomialData i j) := by
  rw [← permutedSixOutputThreeTail_computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

end FD56
