/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SevenSevenTangentRank
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

def sevenSevenTangentU : Fin 5 → R[X] := fun i=>integerPolynomial (sevenSevenTangentUData i)
def sevenSevenTangentV : Fin 5 → R[X] := fun i=>integerPolynomial (sevenSevenTangentVData i)

def sevenSevenTangentWitness : Matrix (Fin 5) (Fin 10) R[X] :=
  fiveOutputPluckerTangent (twoColumnWedge sevenSevenTangentU sevenSevenTangentV)

private def wedgeData (i j:Fin 5) : List ℤ :=
  integerPolynomialAdd (integerPolynomialMul (sevenSevenTangentUData i) (sevenSevenTangentVData j))
    ((integerPolynomialMul (sevenSevenTangentUData j) (sevenSevenTangentVData i)).map (-·))

private def computedData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![wedgeData 2 3,(wedgeData 1 3).map (-·),wedgeData 1 2,[],wedgeData 0 3,(wedgeData 0 2).map (-·),[],wedgeData 0 1,[],[]],
    ![wedgeData 2 4,(wedgeData 1 4).map (-·),[],wedgeData 1 2,wedgeData 0 4,[],(wedgeData 0 2).map (-·),[],wedgeData 0 1,[]],
    ![wedgeData 3 4,[],(wedgeData 1 4).map (-·),wedgeData 1 3,[],wedgeData 0 4,(wedgeData 0 3).map (-·),[],[],wedgeData 0 1],
    ![[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,[],[],[],wedgeData 0 4,(wedgeData 0 3).map (-·),wedgeData 0 2],
    ![[],[],[],[],wedgeData 3 4,(wedgeData 2 4).map (-·),wedgeData 2 3,wedgeData 1 4,(wedgeData 1 3).map (-·),wedgeData 1 2]]

def sevenSevenTangentPolynomialData : Matrix (Fin 5) (Fin 10) (List ℤ) :=
  ![![[1,0,0,0,0,0,0,0,1],[0,1,0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,-1,-1],[],[0,0,0,-1,0,0,0,-1],[-1,0,0,0,0,0,0,0,0,0,0,0,1],[],[0,-1,0,0,0,0,0,0,0,0,0,0,0,0,-1],[],[]],
    ![[0,0,0,-1,0,0,0,0,0,0,0,-1],[0,0,0,0,-1,0,0,0,0,0,0,0,0,1],[],[0,0,0,0,0,0,-1,-1],[0,0,0,0,0,0,1,0,0,0,1],[],[-1,0,0,0,0,0,0,0,0,0,0,0,1],[],[0,-1,0,0,0,0,0,0,0,0,0,0,0,0,-1],[]],
    ![[],[],[0,0,0,0,-1,0,0,0,0,0,0,0,0,1],[0,-1,0,0,0,0,0,0,0,0,1],[],[0,0,0,0,0,0,1,0,0,0,1],[0,0,0,1,0,0,0,1],[],[],[0,-1,0,0,0,0,0,0,0,0,0,0,0,0,-1]],
    ![[],[],[0,0,0,1,0,0,0,0,0,0,0,1],[1,0,0,0,0,0,0,0,1],[],[],[],[0,0,0,0,0,0,1,0,0,0,1],[0,0,0,1,0,0,0,1],[1,0,0,0,0,0,0,0,0,0,0,0,-1]],
    ![[],[],[],[],[],[0,0,0,1,0,0,0,0,0,0,0,1],[1,0,0,0,0,0,0,0,1],[0,0,0,0,1,0,0,0,0,0,0,0,0,-1],[0,1,0,0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,-1,-1]]]

private theorem polynomial_row0 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 0 j)=integerPolynomialTrim (sevenSevenTangentPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 1 j)=integerPolynomialTrim (sevenSevenTangentPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 2 j)=integerPolynomialTrim (sevenSevenTangentPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 3 j)=integerPolynomialTrim (sevenSevenTangentPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀j:Fin 10,
    integerPolynomialTrim (computedData 4 j)=integerPolynomialTrim (sevenSevenTangentPolynomialData 4 j) := by decide +kernel

private theorem computed_polynomial (i:Fin 5) (j:Fin 10) :
    integerPolynomial (K:=R) (computedData i j)=sevenSevenTangentWitness i j := by
  fin_cases i <;> fin_cases j <;>
    simp [computedData,sevenSevenTangentWitness,fiveOutputPluckerTangent,wedgeData,
      integerPolynomial_add,integerPolynomial_mul,integerPolynomial_neg,
      sevenSevenTangentU,sevenSevenTangentV,twoColumnWedge,sub_eq_add_neg]

attribute [local irreducible] computedData sevenSevenTangentPolynomialData

private theorem polynomial_data_correct (i:Fin 5) (j:Fin 10) :
    integerPolynomialTrim (computedData i j)=integerPolynomialTrim (sevenSevenTangentPolynomialData i j) := by
  fin_cases i
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j

theorem sevenSevenTangentWitness_entry (i:Fin 5) (j:Fin 10) :
    sevenSevenTangentWitness (R:=R) i j=integerPolynomial (sevenSevenTangentPolynomialData i j) := by
  rw [← computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sevenSevenTangentCoefficientRows (i:Fin 40) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 18 ≃ Fin 90).symm (sevenSevenTangentSelectedRows i)
  (r.1,r.2.val)

def sevenSevenTangentSelectedIntegerEntry (i j:Fin 40) : ℤ :=
  let r := sevenSevenTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm j
  if c.2.val≤r.2 then (sevenSevenTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sevenSevenTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 40) (Fin 40) K :=
  (selectedPolynomialCoefficientMatrix (sevenSevenTangentWitness (R:=K)) 3
    sevenSevenTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 40) :
    sevenSevenTangentSelectedCoefficient (K:=K) i j=(sevenSevenTangentSelectedIntegerEntry i j : K) := by
  dsimp only [sevenSevenTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sevenSevenTangentSelectedIntegerEntry]
  rw [sevenSevenTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 0 j%101=(sevenSevenTangentSelectedData 0 j:ℤ) := by decide +kernel

private theorem selected_row1 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 1 j%101=(sevenSevenTangentSelectedData 1 j:ℤ) := by decide +kernel

private theorem selected_row2 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 2 j%101=(sevenSevenTangentSelectedData 2 j:ℤ) := by decide +kernel

private theorem selected_row3 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 3 j%101=(sevenSevenTangentSelectedData 3 j:ℤ) := by decide +kernel

private theorem selected_row4 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 4 j%101=(sevenSevenTangentSelectedData 4 j:ℤ) := by decide +kernel

private theorem selected_row5 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 5 j%101=(sevenSevenTangentSelectedData 5 j:ℤ) := by decide +kernel

private theorem selected_row6 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 6 j%101=(sevenSevenTangentSelectedData 6 j:ℤ) := by decide +kernel

private theorem selected_row7 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 7 j%101=(sevenSevenTangentSelectedData 7 j:ℤ) := by decide +kernel

private theorem selected_row8 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 8 j%101=(sevenSevenTangentSelectedData 8 j:ℤ) := by decide +kernel

private theorem selected_row9 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 9 j%101=(sevenSevenTangentSelectedData 9 j:ℤ) := by decide +kernel

private theorem selected_row10 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 10 j%101=(sevenSevenTangentSelectedData 10 j:ℤ) := by decide +kernel

private theorem selected_row11 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 11 j%101=(sevenSevenTangentSelectedData 11 j:ℤ) := by decide +kernel

private theorem selected_row12 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 12 j%101=(sevenSevenTangentSelectedData 12 j:ℤ) := by decide +kernel

private theorem selected_row13 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 13 j%101=(sevenSevenTangentSelectedData 13 j:ℤ) := by decide +kernel

private theorem selected_row14 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 14 j%101=(sevenSevenTangentSelectedData 14 j:ℤ) := by decide +kernel

private theorem selected_row15 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 15 j%101=(sevenSevenTangentSelectedData 15 j:ℤ) := by decide +kernel

private theorem selected_row16 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 16 j%101=(sevenSevenTangentSelectedData 16 j:ℤ) := by decide +kernel

private theorem selected_row17 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 17 j%101=(sevenSevenTangentSelectedData 17 j:ℤ) := by decide +kernel

private theorem selected_row18 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 18 j%101=(sevenSevenTangentSelectedData 18 j:ℤ) := by decide +kernel

private theorem selected_row19 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 19 j%101=(sevenSevenTangentSelectedData 19 j:ℤ) := by decide +kernel

private theorem selected_row20 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 20 j%101=(sevenSevenTangentSelectedData 20 j:ℤ) := by decide +kernel

private theorem selected_row21 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 21 j%101=(sevenSevenTangentSelectedData 21 j:ℤ) := by decide +kernel

private theorem selected_row22 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 22 j%101=(sevenSevenTangentSelectedData 22 j:ℤ) := by decide +kernel

private theorem selected_row23 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 23 j%101=(sevenSevenTangentSelectedData 23 j:ℤ) := by decide +kernel

private theorem selected_row24 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 24 j%101=(sevenSevenTangentSelectedData 24 j:ℤ) := by decide +kernel

private theorem selected_row25 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 25 j%101=(sevenSevenTangentSelectedData 25 j:ℤ) := by decide +kernel

private theorem selected_row26 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 26 j%101=(sevenSevenTangentSelectedData 26 j:ℤ) := by decide +kernel

private theorem selected_row27 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 27 j%101=(sevenSevenTangentSelectedData 27 j:ℤ) := by decide +kernel

private theorem selected_row28 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 28 j%101=(sevenSevenTangentSelectedData 28 j:ℤ) := by decide +kernel

private theorem selected_row29 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 29 j%101=(sevenSevenTangentSelectedData 29 j:ℤ) := by decide +kernel

private theorem selected_row30 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 30 j%101=(sevenSevenTangentSelectedData 30 j:ℤ) := by decide +kernel

private theorem selected_row31 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 31 j%101=(sevenSevenTangentSelectedData 31 j:ℤ) := by decide +kernel

private theorem selected_row32 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 32 j%101=(sevenSevenTangentSelectedData 32 j:ℤ) := by decide +kernel

private theorem selected_row33 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 33 j%101=(sevenSevenTangentSelectedData 33 j:ℤ) := by decide +kernel

private theorem selected_row34 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 34 j%101=(sevenSevenTangentSelectedData 34 j:ℤ) := by decide +kernel

private theorem selected_row35 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 35 j%101=(sevenSevenTangentSelectedData 35 j:ℤ) := by decide +kernel

private theorem selected_row36 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 36 j%101=(sevenSevenTangentSelectedData 36 j:ℤ) := by decide +kernel

private theorem selected_row37 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 37 j%101=(sevenSevenTangentSelectedData 37 j:ℤ) := by decide +kernel

private theorem selected_row38 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 38 j%101=(sevenSevenTangentSelectedData 38 j:ℤ) := by decide +kernel

private theorem selected_row39 : ∀j:Fin 40,
    sevenSevenTangentSelectedIntegerEntry 39 j%101=(sevenSevenTangentSelectedData 39 j:ℤ) := by decide +kernel

attribute [local irreducible] sevenSevenTangentSelectedIntegerEntry sevenSevenTangentSelectedData

private theorem selected_integer_entries (i j:Fin 40) :
    sevenSevenTangentSelectedIntegerEntry i j%101=(sevenSevenTangentSelectedData i j:ℤ) := by
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

theorem sevenSevenTangent_selected_integer_binding {K : Type*} [Field K] :
    sevenSevenTangentSelectedCoefficient (K:=K) =
      Matrix.map sevenSevenTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sevenSevenTangent_selected_binding :
    sevenSevenTangentSelectedCoefficient (K:=ZMod 101)=sevenSevenTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sevenSevenTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sevenSevenTangentSelected] using h2

theorem sevenSevenTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (sevenSevenTangentU (R:=R) i).natDegree≤7 := by
  have hl : ∀i:Fin 5,(sevenSevenTangentUData i).length≤8 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sevenSevenTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem sevenSevenTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (sevenSevenTangentV (R:=R) i).natDegree≤7 := by
  have hl : ∀i:Fin 5,(sevenSevenTangentVData i).length≤8 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sevenSevenTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (sevenSevenTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sevenSevenTangentWitness (R:=K)) 3 sevenSevenTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 4) ≃ Fin 40 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (sevenSevenTangentWitness (R:=K))
    3 sevenSevenTangentCoefficientRows
  have he : M=(sevenSevenTangentSelectedCoefficient (K:=K)).submatrix id e := by
    funext i j
    change M i j=M i (e.symm (e j))
    rw [Equiv.symm_apply_apply]
  change Function.Injective M.mulVec
  have hM : Function.Injective M.mulVec := by
    rw [he]
    intro x y hxy
    simp only [Matrix.submatrix_mulVec_equiv,Function.comp_id] at hxy
    have h := hinj hxy
    funext j
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun h (e j)
  exact hM

theorem sevenSevenTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : sevenSevenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    sevenSevenTangentWitness 3 sevenSevenTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [sevenSevenTangent_selected_binding]
  exact sevenSevenTangentSelected_injective

theorem sevenSevenTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sevenSevenTangentWitness (R:=K)) 3 sevenSevenTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [sevenSevenTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sevenSevenTangent_selected_integer_binding, sevenSevenTangent_selected_binding]
  exact sevenSevenTangentSelected_injective

theorem sevenSevenTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : sevenSevenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    sevenSevenTangentWitness 3 sevenSevenTangentCoefficientRows
      sevenSevenTangent_coefficient_injective_charZero v hv hdeg


end FD56
