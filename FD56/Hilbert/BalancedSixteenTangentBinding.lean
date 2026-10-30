/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSixteenTangentRank
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

def balancedSixteenTangentU : Fin 5 → R[X] := fun i=>integerPolynomial (balancedSixteenTangentUData i)
def balancedSixteenTangentV : Fin 5 → R[X] := fun i=>integerPolynomial (balancedSixteenTangentVData i)

def balancedSixteenTangentWitness : Matrix (Fin 5) (Fin 10) R[X] :=
  fiveOutputPluckerTangent (twoColumnWedge balancedSixteenTangentU balancedSixteenTangentV)

private def wedgeData (i j:Fin 5) : List ℤ :=
  integerPolynomialAdd (integerPolynomialMul (balancedSixteenTangentUData i) (balancedSixteenTangentVData j))
    ((integerPolynomialMul (balancedSixteenTangentUData j) (balancedSixteenTangentVData i)).map (-·))

private def computedData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![wedgeData 2 3,(wedgeData 1 3).map (-·),wedgeData 1 2,[],wedgeData 0 3,(wedgeData 0 2).map (-·),[],wedgeData 0 1,[],[]],
    ![wedgeData 2 4,(wedgeData 1 4).map (-·),[],wedgeData 1 2,wedgeData 0 4,[],(wedgeData 0 2).map (-·),[],wedgeData 0 1,[]],
    ![wedgeData 3 4,[],(wedgeData 1 4).map (-·),wedgeData 1 3,[],wedgeData 0 4,(wedgeData 0 3).map (-·),[],[],wedgeData 0 1],
    ![[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,[],[],[],wedgeData 0 4,(wedgeData 0 3).map (-·),wedgeData 0 2],
    ![[],[],[],[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,wedgeData 1 4,(wedgeData 1 3).map (-·),wedgeData 1 2]]

def balancedSixteenTangentPolynomialData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![[0,0,0,0,-1,0,0,1],[0,1,0,0,0,0,0,0,0,1],[0,0,0,1,0,0,0,0,0,0,0,1],[],[0,-1,0,0,0,0,0,0,-1,-1],[0,0,0,0,0,0,-1,0,0,0,-1,0,0,0,-1],[],[-1,0,0,0,0,0,0,0,-2,0,0,0,0,0,0,0,-1],[],[]],
    ![[0,0,0,0,0,0,0,1,0,0,0,1],[0,0,0,0,0,1,0,0,0,0,0,0,0,1],[],[0,0,0,1,0,0,0,0,0,0,0,1],[0,0,0,0,1],[],[0,0,0,0,0,0,-1,0,0,0,-1,0,0,0,-1],[],[-1,0,0,0,0,0,0,0,-2,0,0,0,0,0,0,0,-1],[]],
    ![[0,0,0,0,0,-1,-1],[],[0,0,0,0,0,1,0,0,0,0,0,0,0,1],[0,-1,0,0,0,0,0,0,0,-1],[],[0,0,0,0,1],[0,1,0,0,0,0,0,0,1,1],[],[],[-1,0,0,0,0,0,0,0,-2,0,0,0,0,0,0,0,-1]],
    ![[],[0,0,0,0,0,-1,-1],[0,0,0,0,0,0,0,-1,0,0,0,-1],[0,0,0,0,-1,0,0,1],[],[],[],[0,0,0,0,1],[0,1,0,0,0,0,0,0,1,1],[0,0,0,0,0,0,1,0,0,0,1,0,0,0,1]],
    ![[],[],[],[],[0,0,0,0,0,-1,-1],[0,0,0,0,0,0,0,-1,0,0,0,-1],[0,0,0,0,-1,0,0,1],[0,0,0,0,0,-1,0,0,0,0,0,0,0,-1],[0,1,0,0,0,0,0,0,0,1],[0,0,0,1,0,0,0,0,0,0,0,1]]]

private theorem polynomial_row0 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 0 j)=integerPolynomialTrim (balancedSixteenTangentPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 1 j)=integerPolynomialTrim (balancedSixteenTangentPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 2 j)=integerPolynomialTrim (balancedSixteenTangentPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 3 j)=integerPolynomialTrim (balancedSixteenTangentPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 4 j)=integerPolynomialTrim (balancedSixteenTangentPolynomialData 4 j) := by decide +kernel

private theorem computed_polynomial (i:Fin 5) (j:Fin 10) :
    integerPolynomial (K:=R) (computedData i j)=balancedSixteenTangentWitness i j := by
  fin_cases i <;> fin_cases j <;>
    simp [computedData,balancedSixteenTangentWitness,fiveOutputPluckerTangent,wedgeData,
      integerPolynomial_add,integerPolynomial_mul,integerPolynomial_neg,
      balancedSixteenTangentU,balancedSixteenTangentV,twoColumnWedge,sub_eq_add_neg]

attribute [local irreducible] computedData balancedSixteenTangentPolynomialData

private theorem polynomial_data_correct (i:Fin 5) (j:Fin 10) :
    integerPolynomialTrim (computedData i j)=integerPolynomialTrim (balancedSixteenTangentPolynomialData i j) := by
  fin_cases i
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j

theorem balancedSixteenTangentWitness_entry (i:Fin 5) (j:Fin 10) :
    balancedSixteenTangentWitness (R:=R) i j=integerPolynomial (balancedSixteenTangentPolynomialData i j) := by
  rw [← computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedSixteenTangentCoefficientRows (i:Fin 40) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 20 ≃ Fin 100).symm (balancedSixteenTangentSelectedRows i)
  (r.1,r.2.val)

def balancedSixteenTangentSelectedIntegerEntry (i j:Fin 40) : ℤ :=
  let r := balancedSixteenTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm j
  if c.2.val≤r.2 then (balancedSixteenTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedSixteenTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 40) (Fin 40) K :=
  (selectedPolynomialCoefficientMatrix (balancedSixteenTangentWitness (R:=K)) 3
    balancedSixteenTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 40) :
    balancedSixteenTangentSelectedCoefficient (K:=K) i j=(balancedSixteenTangentSelectedIntegerEntry i j : K) := by
  dsimp only [balancedSixteenTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedSixteenTangentSelectedIntegerEntry]
  rw [balancedSixteenTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 0 j%101=(balancedSixteenTangentSelectedData 0 j:ℤ) := by decide +kernel

private theorem selected_row1 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 1 j%101=(balancedSixteenTangentSelectedData 1 j:ℤ) := by decide +kernel

private theorem selected_row2 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 2 j%101=(balancedSixteenTangentSelectedData 2 j:ℤ) := by decide +kernel

private theorem selected_row3 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 3 j%101=(balancedSixteenTangentSelectedData 3 j:ℤ) := by decide +kernel

private theorem selected_row4 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 4 j%101=(balancedSixteenTangentSelectedData 4 j:ℤ) := by decide +kernel

private theorem selected_row5 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 5 j%101=(balancedSixteenTangentSelectedData 5 j:ℤ) := by decide +kernel

private theorem selected_row6 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 6 j%101=(balancedSixteenTangentSelectedData 6 j:ℤ) := by decide +kernel

private theorem selected_row7 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 7 j%101=(balancedSixteenTangentSelectedData 7 j:ℤ) := by decide +kernel

private theorem selected_row8 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 8 j%101=(balancedSixteenTangentSelectedData 8 j:ℤ) := by decide +kernel

private theorem selected_row9 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 9 j%101=(balancedSixteenTangentSelectedData 9 j:ℤ) := by decide +kernel

private theorem selected_row10 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 10 j%101=(balancedSixteenTangentSelectedData 10 j:ℤ) := by decide +kernel

private theorem selected_row11 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 11 j%101=(balancedSixteenTangentSelectedData 11 j:ℤ) := by decide +kernel

private theorem selected_row12 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 12 j%101=(balancedSixteenTangentSelectedData 12 j:ℤ) := by decide +kernel

private theorem selected_row13 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 13 j%101=(balancedSixteenTangentSelectedData 13 j:ℤ) := by decide +kernel

private theorem selected_row14 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 14 j%101=(balancedSixteenTangentSelectedData 14 j:ℤ) := by decide +kernel

private theorem selected_row15 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 15 j%101=(balancedSixteenTangentSelectedData 15 j:ℤ) := by decide +kernel

private theorem selected_row16 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 16 j%101=(balancedSixteenTangentSelectedData 16 j:ℤ) := by decide +kernel

private theorem selected_row17 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 17 j%101=(balancedSixteenTangentSelectedData 17 j:ℤ) := by decide +kernel

private theorem selected_row18 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 18 j%101=(balancedSixteenTangentSelectedData 18 j:ℤ) := by decide +kernel

private theorem selected_row19 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 19 j%101=(balancedSixteenTangentSelectedData 19 j:ℤ) := by decide +kernel

private theorem selected_row20 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 20 j%101=(balancedSixteenTangentSelectedData 20 j:ℤ) := by decide +kernel

private theorem selected_row21 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 21 j%101=(balancedSixteenTangentSelectedData 21 j:ℤ) := by decide +kernel

private theorem selected_row22 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 22 j%101=(balancedSixteenTangentSelectedData 22 j:ℤ) := by decide +kernel

private theorem selected_row23 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 23 j%101=(balancedSixteenTangentSelectedData 23 j:ℤ) := by decide +kernel

private theorem selected_row24 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 24 j%101=(balancedSixteenTangentSelectedData 24 j:ℤ) := by decide +kernel

private theorem selected_row25 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 25 j%101=(balancedSixteenTangentSelectedData 25 j:ℤ) := by decide +kernel

private theorem selected_row26 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 26 j%101=(balancedSixteenTangentSelectedData 26 j:ℤ) := by decide +kernel

private theorem selected_row27 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 27 j%101=(balancedSixteenTangentSelectedData 27 j:ℤ) := by decide +kernel

private theorem selected_row28 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 28 j%101=(balancedSixteenTangentSelectedData 28 j:ℤ) := by decide +kernel

private theorem selected_row29 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 29 j%101=(balancedSixteenTangentSelectedData 29 j:ℤ) := by decide +kernel

private theorem selected_row30 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 30 j%101=(balancedSixteenTangentSelectedData 30 j:ℤ) := by decide +kernel

private theorem selected_row31 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 31 j%101=(balancedSixteenTangentSelectedData 31 j:ℤ) := by decide +kernel

private theorem selected_row32 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 32 j%101=(balancedSixteenTangentSelectedData 32 j:ℤ) := by decide +kernel

private theorem selected_row33 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 33 j%101=(balancedSixteenTangentSelectedData 33 j:ℤ) := by decide +kernel

private theorem selected_row34 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 34 j%101=(balancedSixteenTangentSelectedData 34 j:ℤ) := by decide +kernel

private theorem selected_row35 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 35 j%101=(balancedSixteenTangentSelectedData 35 j:ℤ) := by decide +kernel

private theorem selected_row36 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 36 j%101=(balancedSixteenTangentSelectedData 36 j:ℤ) := by decide +kernel

private theorem selected_row37 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 37 j%101=(balancedSixteenTangentSelectedData 37 j:ℤ) := by decide +kernel

private theorem selected_row38 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 38 j%101=(balancedSixteenTangentSelectedData 38 j:ℤ) := by decide +kernel

private theorem selected_row39 : ∀j:Fin 40,
    balancedSixteenTangentSelectedIntegerEntry 39 j%101=(balancedSixteenTangentSelectedData 39 j:ℤ) := by decide +kernel

attribute [local irreducible] balancedSixteenTangentSelectedIntegerEntry balancedSixteenTangentSelectedData

private theorem selected_integer_entries (i j:Fin 40) :
    balancedSixteenTangentSelectedIntegerEntry i j%101=(balancedSixteenTangentSelectedData i j:ℤ) := by
  fin_cases i
  · exact selected_row0 j
  · exact selected_row1 j
  · exact selected_row2 j
  · exact selected_row3 j
  · exact selected_row4 j
  · exact selected_row5 j
  · exact selected_row6 j
  · exact selected_row7 j
  · exact selected_row8 j
  · exact selected_row9 j
  · exact selected_row10 j
  · exact selected_row11 j
  · exact selected_row12 j
  · exact selected_row13 j
  · exact selected_row14 j
  · exact selected_row15 j
  · exact selected_row16 j
  · exact selected_row17 j
  · exact selected_row18 j
  · exact selected_row19 j
  · exact selected_row20 j
  · exact selected_row21 j
  · exact selected_row22 j
  · exact selected_row23 j
  · exact selected_row24 j
  · exact selected_row25 j
  · exact selected_row26 j
  · exact selected_row27 j
  · exact selected_row28 j
  · exact selected_row29 j
  · exact selected_row30 j
  · exact selected_row31 j
  · exact selected_row32 j
  · exact selected_row33 j
  · exact selected_row34 j
  · exact selected_row35 j
  · exact selected_row36 j
  · exact selected_row37 j
  · exact selected_row38 j
  · exact selected_row39 j

theorem balancedSixteenTangent_selected_integer_binding {K : Type*} [Field K] :
    balancedSixteenTangentSelectedCoefficient (K:=K) =
      Matrix.map balancedSixteenTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedSixteenTangent_selected_binding :
    balancedSixteenTangentSelectedCoefficient (K:=ZMod 101)=balancedSixteenTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedSixteenTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedSixteenTangentSelected] using h2

end FD56
