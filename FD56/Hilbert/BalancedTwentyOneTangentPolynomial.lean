/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentData
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import FD56.LinearAlgebra.RankSpecializationExtension
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.FiveOutputPluckerTangent

/-! An integral two-column frame and its exact Plucker tangent matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
variable {R : Type*} [CommRing R]

def balancedTwentyOneTangentU : Fin 5 → R[X] := fun i=>integerPolynomial (balancedTwentyOneTangentUData i)
def balancedTwentyOneTangentV : Fin 5 → R[X] := fun i=>integerPolynomial (balancedTwentyOneTangentVData i)

def balancedTwentyOneTangentWitness : Matrix (Fin 5) (Fin 10) R[X] :=
  fiveOutputPluckerTangent (twoColumnWedge balancedTwentyOneTangentU balancedTwentyOneTangentV)

private def wedgeData (i j:Fin 5) : List ℤ :=
  integerPolynomialAdd (integerPolynomialMul (balancedTwentyOneTangentUData i) (balancedTwentyOneTangentVData j))
    ((integerPolynomialMul (balancedTwentyOneTangentUData j) (balancedTwentyOneTangentVData i)).map (-·))

private def computedData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![wedgeData 2 3,(wedgeData 1 3).map (-·),wedgeData 1 2,[],wedgeData 0 3,(wedgeData 0 2).map (-·),[],wedgeData 0 1,[],[]],
    ![wedgeData 2 4,(wedgeData 1 4).map (-·),[],wedgeData 1 2,wedgeData 0 4,[],(wedgeData 0 2).map (-·),[],wedgeData 0 1,[]],
    ![wedgeData 3 4,[],(wedgeData 1 4).map (-·),wedgeData 1 3,[],wedgeData 0 4,(wedgeData 0 3).map (-·),[],[],wedgeData 0 1],
    ![[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,[],[],[],wedgeData 0 4,(wedgeData 0 3).map (-·),wedgeData 0 2],
    ![[],[],[],[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,wedgeData 1 4,(wedgeData 1 3).map (-·),wedgeData 1 2]]

def balancedTwentyOneTangentPolynomialData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1],[0,0,0,0,0,0,-1,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,-1],[],[0,0,0,0,1,0,0,1,-1,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,0,0,0,1],[],[-1,0,0,-1,0,1,0,0,1,0,-1,0,0,0,0,1],[],[]],
    ![[0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,-1],[0,0,-1,0,0,0,0,1],[],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,-1],[0,0,0,0,-1,0,0,0,0,0,-1,0,0,-1,0,0,0,0,0,0,-1],[],[0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,0,0,0,1],[],[-1,0,0,-1,0,1,0,0,1,0,-1,0,0,0,0,1],[]],
    ![[0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,-1],[],[0,0,-1,0,0,0,0,1],[0,0,0,0,0,0,1,0,0,0,0,-1],[],[0,0,0,0,-1,0,0,0,0,0,-1,0,0,-1,0,0,0,0,0,0,-1],[0,0,0,0,-1,0,0,-1,1,0,0,0,0,0,-1],[],[],[-1,0,0,-1,0,1,0,0,1,0,-1,0,0,0,0,1]],
    ![[],[0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1],[],[],[],[0,0,0,0,-1,0,0,0,0,0,-1,0,0,-1,0,0,0,0,0,0,-1],[0,0,0,0,-1,0,0,-1,1,0,0,0,0,0,-1],[0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,-1,0,0,0,0,0,0,-1]],
    ![[],[],[],[],[0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1],[0,0,1,0,0,0,0,-1],[0,0,0,0,0,0,-1,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,-1]]]

private theorem polynomial_row0 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 0 j)=integerPolynomialTrim (balancedTwentyOneTangentPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 1 j)=integerPolynomialTrim (balancedTwentyOneTangentPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 2 j)=integerPolynomialTrim (balancedTwentyOneTangentPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 3 j)=integerPolynomialTrim (balancedTwentyOneTangentPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 4 j)=integerPolynomialTrim (balancedTwentyOneTangentPolynomialData 4 j) := by decide +kernel

private theorem computed_polynomial (i:Fin 5) (j:Fin 10) :
    integerPolynomial (K:=R) (computedData i j)=balancedTwentyOneTangentWitness i j := by
  fin_cases i <;> fin_cases j <;>
    simp [computedData,balancedTwentyOneTangentWitness,fiveOutputPluckerTangent,wedgeData,
      integerPolynomial_add,integerPolynomial_mul,integerPolynomial_neg,
      balancedTwentyOneTangentU,balancedTwentyOneTangentV,twoColumnWedge,sub_eq_add_neg]

attribute [local irreducible] computedData balancedTwentyOneTangentPolynomialData

private theorem polynomial_data_correct (i:Fin 5) (j:Fin 10) :
    integerPolynomialTrim (computedData i j)=integerPolynomialTrim (balancedTwentyOneTangentPolynomialData i j) := by
  fin_cases i
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j

theorem balancedTwentyOneTangentWitness_entry (i:Fin 5) (j:Fin 10) :
    balancedTwentyOneTangentWitness (R:=R) i j=integerPolynomial (balancedTwentyOneTangentPolynomialData i j) := by
  rw [← computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

end FD56
