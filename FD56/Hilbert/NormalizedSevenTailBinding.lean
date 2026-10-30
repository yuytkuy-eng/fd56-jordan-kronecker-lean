/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedSevenTailRank
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

def normalizedSevenTailU : Fin 5 → R[X] := fun i=>integerPolynomial (normalizedSevenTailUData i)
def normalizedSevenTailV : Fin 5 → R[X] := fun i=>integerPolynomial (normalizedSevenTailVData i)

def normalizedSevenTailWitness : Matrix (Fin 5) (Fin 10) R[X] :=
  fiveOutputPluckerTangent (twoColumnWedge normalizedSevenTailU normalizedSevenTailV)

private def wedgeData (i j:Fin 5) : List ℤ :=
  integerPolynomialAdd (integerPolynomialMul (normalizedSevenTailUData i) (normalizedSevenTailVData j))
    ((integerPolynomialMul (normalizedSevenTailUData j) (normalizedSevenTailVData i)).map (-·))

private def computedData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![wedgeData 2 3,(wedgeData 1 3).map (-·),wedgeData 1 2,[],wedgeData 0 3,(wedgeData 0 2).map (-·),[],wedgeData 0 1,[],[]],
    ![wedgeData 2 4,(wedgeData 1 4).map (-·),[],wedgeData 1 2,wedgeData 0 4,[],(wedgeData 0 2).map (-·),[],wedgeData 0 1,[]],
    ![wedgeData 3 4,[],(wedgeData 1 4).map (-·),wedgeData 1 3,[],wedgeData 0 4,(wedgeData 0 3).map (-·),[],[],wedgeData 0 1],
    ![[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,[],[],[],wedgeData 0 4,(wedgeData 0 3).map (-·),wedgeData 0 2],
    ![[],[],[],[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,wedgeData 1 4,(wedgeData 1 3).map (-·),wedgeData 1 2]]

def normalizedSevenTailPolynomialData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![[0,0,0,-1],[0,0,-1,0,0,0,0,-1,1,-1],[0,0,0,0,0,1],[],[0,0,0,0,-1,0,0,0,0,0,0,-1],[0,-1,0,0,0,0,0,0,-1],[],[-1,0,0,0,0,-1,0,-2,0,0,0,0,-1,0,-1],[],[]],
    ![[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1,0,0,0,1,1,0,1],[],[0,0,0,0,0,1],[0,0,0,0,0,0,-1,0,0,0,0,0,0,-1],[],[0,-1,0,0,0,0,0,0,-1],[],[-1,0,0,0,0,-1,0,-2,0,0,0,0,-1,0,-1],[]],
    ![[0,0,0,0,0,0,0,0,-1,0,-1],[],[0,0,0,0,0,0,1,0,0,0,1,1,0,1],[0,0,1,0,0,0,0,1,-1,1],[],[0,0,0,0,0,0,-1,0,0,0,0,0,0,-1],[0,0,0,0,1,0,0,0,0,0,0,1],[],[],[-1,0,0,0,0,-1,0,-2,0,0,0,0,-1,0,-1]],
    ![[],[0,0,0,0,0,0,0,0,-1,0,-1],[0,0,0,0,0,0,0,-1],[0,0,0,-1],[],[],[],[0,0,0,0,0,0,-1,0,0,0,0,0,0,-1],[0,0,0,0,1,0,0,0,0,0,0,1],[0,1,0,0,0,0,0,0,1]],
    ![[],[],[],[],[0,0,0,0,0,0,0,0,-1,0,-1],[0,0,0,0,0,0,0,-1],[0,0,0,-1],[0,0,0,0,0,0,-1,0,0,0,-1,-1,0,-1],[0,0,-1,0,0,0,0,-1,1,-1],[0,0,0,0,0,1]]]

private theorem polynomial_row0 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 0 j)=integerPolynomialTrim (normalizedSevenTailPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 1 j)=integerPolynomialTrim (normalizedSevenTailPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 2 j)=integerPolynomialTrim (normalizedSevenTailPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 3 j)=integerPolynomialTrim (normalizedSevenTailPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 4 j)=integerPolynomialTrim (normalizedSevenTailPolynomialData 4 j) := by decide +kernel

private theorem computed_polynomial (i:Fin 5) (j:Fin 10) :
    integerPolynomial (K:=R) (computedData i j)=normalizedSevenTailWitness i j := by
  fin_cases i <;> fin_cases j <;>
    simp [computedData,normalizedSevenTailWitness,fiveOutputPluckerTangent,wedgeData,
      integerPolynomial_add,integerPolynomial_mul,integerPolynomial_neg,
      normalizedSevenTailU,normalizedSevenTailV,twoColumnWedge,sub_eq_add_neg]

attribute [local irreducible] computedData normalizedSevenTailPolynomialData

private theorem polynomial_data_correct (i:Fin 5) (j:Fin 10) :
    integerPolynomialTrim (computedData i j)=integerPolynomialTrim (normalizedSevenTailPolynomialData i j) := by
  fin_cases i
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j

theorem normalizedSevenTailWitness_entry (i:Fin 5) (j:Fin 10) :
    normalizedSevenTailWitness (R:=R) i j=integerPolynomial (normalizedSevenTailPolynomialData i j) := by
  rw [← computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def normalizedSevenTailCoefficientRows (i:Fin 40) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 18 ≃ Fin 90).symm (normalizedSevenTailSelectedRows i)
  (r.1,r.2.val)

def normalizedSevenTailSelectedIntegerEntry (i j:Fin 40) : ℤ :=
  let r := normalizedSevenTailCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm j
  if c.2.val≤r.2 then (normalizedSevenTailPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def normalizedSevenTailSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 40) (Fin 40) K :=
  (selectedPolynomialCoefficientMatrix (normalizedSevenTailWitness (R:=K)) 3
    normalizedSevenTailCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 40) :
    normalizedSevenTailSelectedCoefficient (K:=K) i j=(normalizedSevenTailSelectedIntegerEntry i j : K) := by
  dsimp only [normalizedSevenTailSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,normalizedSevenTailSelectedIntegerEntry]
  rw [normalizedSevenTailWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 0 j%101=(normalizedSevenTailSelectedData 0 j:ℤ) := by decide +kernel

private theorem selected_row1 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 1 j%101=(normalizedSevenTailSelectedData 1 j:ℤ) := by decide +kernel

private theorem selected_row2 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 2 j%101=(normalizedSevenTailSelectedData 2 j:ℤ) := by decide +kernel

private theorem selected_row3 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 3 j%101=(normalizedSevenTailSelectedData 3 j:ℤ) := by decide +kernel

private theorem selected_row4 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 4 j%101=(normalizedSevenTailSelectedData 4 j:ℤ) := by decide +kernel

private theorem selected_row5 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 5 j%101=(normalizedSevenTailSelectedData 5 j:ℤ) := by decide +kernel

private theorem selected_row6 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 6 j%101=(normalizedSevenTailSelectedData 6 j:ℤ) := by decide +kernel

private theorem selected_row7 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 7 j%101=(normalizedSevenTailSelectedData 7 j:ℤ) := by decide +kernel

private theorem selected_row8 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 8 j%101=(normalizedSevenTailSelectedData 8 j:ℤ) := by decide +kernel

private theorem selected_row9 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 9 j%101=(normalizedSevenTailSelectedData 9 j:ℤ) := by decide +kernel

private theorem selected_row10 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 10 j%101=(normalizedSevenTailSelectedData 10 j:ℤ) := by decide +kernel

private theorem selected_row11 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 11 j%101=(normalizedSevenTailSelectedData 11 j:ℤ) := by decide +kernel

private theorem selected_row12 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 12 j%101=(normalizedSevenTailSelectedData 12 j:ℤ) := by decide +kernel

private theorem selected_row13 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 13 j%101=(normalizedSevenTailSelectedData 13 j:ℤ) := by decide +kernel

private theorem selected_row14 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 14 j%101=(normalizedSevenTailSelectedData 14 j:ℤ) := by decide +kernel

private theorem selected_row15 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 15 j%101=(normalizedSevenTailSelectedData 15 j:ℤ) := by decide +kernel

private theorem selected_row16 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 16 j%101=(normalizedSevenTailSelectedData 16 j:ℤ) := by decide +kernel

private theorem selected_row17 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 17 j%101=(normalizedSevenTailSelectedData 17 j:ℤ) := by decide +kernel

private theorem selected_row18 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 18 j%101=(normalizedSevenTailSelectedData 18 j:ℤ) := by decide +kernel

private theorem selected_row19 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 19 j%101=(normalizedSevenTailSelectedData 19 j:ℤ) := by decide +kernel

private theorem selected_row20 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 20 j%101=(normalizedSevenTailSelectedData 20 j:ℤ) := by decide +kernel

private theorem selected_row21 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 21 j%101=(normalizedSevenTailSelectedData 21 j:ℤ) := by decide +kernel

private theorem selected_row22 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 22 j%101=(normalizedSevenTailSelectedData 22 j:ℤ) := by decide +kernel

private theorem selected_row23 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 23 j%101=(normalizedSevenTailSelectedData 23 j:ℤ) := by decide +kernel

private theorem selected_row24 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 24 j%101=(normalizedSevenTailSelectedData 24 j:ℤ) := by decide +kernel

private theorem selected_row25 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 25 j%101=(normalizedSevenTailSelectedData 25 j:ℤ) := by decide +kernel

private theorem selected_row26 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 26 j%101=(normalizedSevenTailSelectedData 26 j:ℤ) := by decide +kernel

private theorem selected_row27 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 27 j%101=(normalizedSevenTailSelectedData 27 j:ℤ) := by decide +kernel

private theorem selected_row28 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 28 j%101=(normalizedSevenTailSelectedData 28 j:ℤ) := by decide +kernel

private theorem selected_row29 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 29 j%101=(normalizedSevenTailSelectedData 29 j:ℤ) := by decide +kernel

private theorem selected_row30 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 30 j%101=(normalizedSevenTailSelectedData 30 j:ℤ) := by decide +kernel

private theorem selected_row31 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 31 j%101=(normalizedSevenTailSelectedData 31 j:ℤ) := by decide +kernel

private theorem selected_row32 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 32 j%101=(normalizedSevenTailSelectedData 32 j:ℤ) := by decide +kernel

private theorem selected_row33 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 33 j%101=(normalizedSevenTailSelectedData 33 j:ℤ) := by decide +kernel

private theorem selected_row34 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 34 j%101=(normalizedSevenTailSelectedData 34 j:ℤ) := by decide +kernel

private theorem selected_row35 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 35 j%101=(normalizedSevenTailSelectedData 35 j:ℤ) := by decide +kernel

private theorem selected_row36 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 36 j%101=(normalizedSevenTailSelectedData 36 j:ℤ) := by decide +kernel

private theorem selected_row37 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 37 j%101=(normalizedSevenTailSelectedData 37 j:ℤ) := by decide +kernel

private theorem selected_row38 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 38 j%101=(normalizedSevenTailSelectedData 38 j:ℤ) := by decide +kernel

private theorem selected_row39 : ∀j:Fin 40,
    normalizedSevenTailSelectedIntegerEntry 39 j%101=(normalizedSevenTailSelectedData 39 j:ℤ) := by decide +kernel

attribute [local irreducible] normalizedSevenTailSelectedIntegerEntry normalizedSevenTailSelectedData

private theorem selected_integer_entries (i j:Fin 40) :
    normalizedSevenTailSelectedIntegerEntry i j%101=(normalizedSevenTailSelectedData i j:ℤ) := by
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

theorem normalizedSevenTail_selected_integer_binding {K : Type*} [Field K] :
    normalizedSevenTailSelectedCoefficient (K:=K) =
      Matrix.map normalizedSevenTailSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem normalizedSevenTail_selected_binding :
    normalizedSevenTailSelectedCoefficient (K:=ZMod 101)=normalizedSevenTailSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (normalizedSevenTailSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,normalizedSevenTailSelected] using h2

end FD56
