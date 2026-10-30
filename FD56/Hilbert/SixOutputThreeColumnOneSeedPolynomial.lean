/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnOneSeedMinors
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Integral coefficients bound to the actual twenty-equation triple tangent. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
variable {R : Type*} [CommRing R]

def sixOutputThreeColumnOneSeedComputedData (r j : Fin 20) : List ℤ :=
  ((sixOutputTriplePluckerTermData r).map fun t =>
    (integerPolynomialAdd
      (if j=t.2.1 then sixOutputThreeColumnOneSeedMinorData t.2.2 else [])
      (if j=t.2.2 then sixOutputThreeColumnOneSeedMinorData t.2.1 else [])).map (t.1*·)).foldr integerPolynomialAdd []

def sixOutputThreeColumnOneSeedPolynomialData : Matrix (Fin 20) (Fin 20) (List ℤ) :=
  ![![[],[0,0,-1],[],[],[],[],[],[0,0,0,-1],[],[],[],[],[],[],[],[],[],[],[],[]],
    ![[],[],[],[],[0,0,-1],[],[],[],[0,0,0,-1],[],[],[],[],[],[],[],[],[],[],[]],
    ![[0,-1],[],[],[0,0,1],[],[0,0,-1],[],[],[],[0,0,0,-1],[],[],[],[],[],[],[],[],[],[]],
    ![[],[],[0,0,-1],[],[],[],[],[],[],[],[],[],[],[0,0,0,-1],[],[],[],[],[],[]],
    ![[0,1],[],[],[0,0,-1],[],[],[],[],[],[],[0,0,-1],[],[],[],[0,0,0,-1],[],[],[],[],[]],
    ![[],[],[],[],[],[],[],[],[],[],[],[0,0,-1],[],[],[],[0,0,0,-1],[],[],[],[]],
    ![[1],[],[],[0,-1],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,-1],[],[],[0,0,0,1]],
    ![[0,-1],[],[],[],[],[0,0,-1],[],[],[],[],[0,0,1],[],[],[],[],[],[0,0,0,-1],[],[],[]],
    ![[],[],[],[],[],[],[0,0,-1],[],[],[],[],[],[],[],[],[],[],[0,0,0,-1],[],[]],
    ![[],[],[],[],[],[],[],[],[],[],[],[],[0,0,-1],[],[],[],[],[],[0,0,0,-1],[]],
    ![[-1],[],[],[0,1],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,1],[],[],[0,0,0,-1]],
    ![[],[-1],[],[],[],[],[],[0,-1],[],[],[],[],[],[],[],[],[],[],[],[]],
    ![[],[],[-1],[],[],[],[],[],[],[],[],[],[],[0,-1],[],[],[],[],[],[]],
    ![[],[],[],[],[-1],[],[],[],[0,-1],[],[],[],[],[],[],[],[],[],[],[]],
    ![[],[],[],[],[],[-1],[],[],[],[0,-1],[],[],[],[],[],[],[0,-1],[],[],[0,0,1]],
    ![[],[],[],[],[],[],[],[],[],[],[-1],[],[],[],[0,-1],[],[0,1],[],[],[0,0,-1]],
    ![[],[],[],[],[],[],[],[],[],[],[],[-1],[],[],[],[0,-1],[],[],[],[]],
    ![[],[],[],[-1],[],[],[],[],[],[0,1],[],[],[],[],[0,-1],[],[],[],[],[0,0,-1]],
    ![[],[],[],[],[],[],[-1],[],[],[],[],[],[],[],[],[],[],[0,-1],[],[]],
    ![[],[],[],[],[],[],[],[],[],[],[],[],[-1],[],[],[],[],[],[0,-1],[]]]

private theorem integerPolynomial_sum (l : List (List ℤ)) :
    integerPolynomial (K:=R) (l.foldr integerPolynomialAdd [])=
      (l.map (integerPolynomial (K:=R))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons,integerPolynomial_add,List.map_cons,List.sum_cons,ih]

theorem sixOutputThreeColumnOneSeed_computed_polynomial (r j : Fin 20) :
    integerPolynomial (K:=R) (sixOutputThreeColumnOneSeedComputedData r j)=sixOutputThreeColumnOneSeedWitness r j := by
  unfold sixOutputThreeColumnOneSeedComputedData sixOutputThreeColumnOneSeedWitness sixOutputTriplePluckerTangent
  rw [sixOutputTriplePluckerTerms_eq_data,integerPolynomial_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  dsimp only [Function.comp_apply]
  rw [integerPolynomial_map_mul,integerPolynomial_add]
  split_ifs <;> simp [← sixOutputThreeColumnOneSeedMinors_entry]


private theorem polynomial_row0 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 0 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 1 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 2 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 3 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 4 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 4 j) := by decide +kernel

private theorem polynomial_row5 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 5 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 5 j) := by decide +kernel

private theorem polynomial_row6 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 6 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 6 j) := by decide +kernel

private theorem polynomial_row7 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 7 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 7 j) := by decide +kernel

private theorem polynomial_row8 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 8 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 8 j) := by decide +kernel

private theorem polynomial_row9 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 9 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 9 j) := by decide +kernel

private theorem polynomial_row10 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 10 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 10 j) := by decide +kernel

private theorem polynomial_row11 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 11 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 11 j) := by decide +kernel

private theorem polynomial_row12 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 12 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 12 j) := by decide +kernel

private theorem polynomial_row13 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 13 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 13 j) := by decide +kernel

private theorem polynomial_row14 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 14 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 14 j) := by decide +kernel

private theorem polynomial_row15 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 15 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 15 j) := by decide +kernel

private theorem polynomial_row16 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 16 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 16 j) := by decide +kernel

private theorem polynomial_row17 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 17 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 17 j) := by decide +kernel

private theorem polynomial_row18 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 18 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 18 j) := by decide +kernel

private theorem polynomial_row19 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData 19 j)=
      integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData 19 j) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnOneSeedComputedData sixOutputThreeColumnOneSeedPolynomialData

private theorem polynomial_data_correct (i j : Fin 20) :
    integerPolynomialTrim (sixOutputThreeColumnOneSeedComputedData i j)=integerPolynomialTrim (sixOutputThreeColumnOneSeedPolynomialData i j) := by
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
  · exact polynomial_row15 j
  · exact polynomial_row16 j
  · exact polynomial_row17 j
  · exact polynomial_row18 j
  · exact polynomial_row19 j

theorem sixOutputThreeColumnOneSeedWitness_entry (i j : Fin 20) :
    sixOutputThreeColumnOneSeedWitness (R:=R) i j=integerPolynomial (sixOutputThreeColumnOneSeedPolynomialData i j) := by
  rw [← sixOutputThreeColumnOneSeed_computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

end FD56
