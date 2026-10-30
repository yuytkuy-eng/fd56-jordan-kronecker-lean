/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PermutedSixOutputThreeTailPolynomial
import FD56.Hilbert.PermutedSixOutputThreeTailRank

/-! Selection of the degree-one tangent coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

def permutedSixOutputThreeTailCoefficientRows (i : Fin 30) : Fin 15 × ℕ :=
  let r := (finProdFinEquiv : Fin 15 × Fin 8 ≃ Fin 120).symm (permutedSixOutputThreeTailSelectedRows i)
  (r.1,r.2.val)

def permutedSixOutputThreeTailSelectedIntegerEntry (i j : Fin 30) : ℤ :=
  let r := permutedSixOutputThreeTailCoefficientRows i
  let c := (finProdFinEquiv : Fin 15 × Fin 2 ≃ Fin 30).symm j
  if c.2.val≤r.2 then (permutedSixOutputThreeTailPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def permutedSixOutputThreeTailSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 30) (Fin 30) K :=
  (selectedPolynomialCoefficientMatrix (permutedSixOutputThreeTailWitness (R:=K)) 1
    permutedSixOutputThreeTailCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 15 × Fin 2 ≃ Fin 30).symm

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_row0 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 0 j%101=(permutedSixOutputThreeTailSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 1 j%101=(permutedSixOutputThreeTailSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 2 j%101=(permutedSixOutputThreeTailSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 3 j%101=(permutedSixOutputThreeTailSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 4 j%101=(permutedSixOutputThreeTailSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 5 j%101=(permutedSixOutputThreeTailSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 6 j%101=(permutedSixOutputThreeTailSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 7 j%101=(permutedSixOutputThreeTailSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 8 j%101=(permutedSixOutputThreeTailSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 9 j%101=(permutedSixOutputThreeTailSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 10 j%101=(permutedSixOutputThreeTailSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 11 j%101=(permutedSixOutputThreeTailSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 12 j%101=(permutedSixOutputThreeTailSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 13 j%101=(permutedSixOutputThreeTailSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 14 j%101=(permutedSixOutputThreeTailSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 15 j%101=(permutedSixOutputThreeTailSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 16 j%101=(permutedSixOutputThreeTailSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 17 j%101=(permutedSixOutputThreeTailSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 18 j%101=(permutedSixOutputThreeTailSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 19 j%101=(permutedSixOutputThreeTailSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 20 j%101=(permutedSixOutputThreeTailSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 21 j%101=(permutedSixOutputThreeTailSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 22 j%101=(permutedSixOutputThreeTailSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 23 j%101=(permutedSixOutputThreeTailSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 24 j%101=(permutedSixOutputThreeTailSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 25 j%101=(permutedSixOutputThreeTailSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 26 j%101=(permutedSixOutputThreeTailSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 27 j%101=(permutedSixOutputThreeTailSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 28 j%101=(permutedSixOutputThreeTailSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 30,
    permutedSixOutputThreeTailSelectedIntegerEntry 29 j%101=(permutedSixOutputThreeTailSelectedData 29 j : ℤ) := by decide +kernel

attribute [local irreducible] permutedSixOutputThreeTailCoefficientRows permutedSixOutputThreeTailPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 30) :
    permutedSixOutputThreeTailSelectedCoefficient (K:=K) i j=(permutedSixOutputThreeTailSelectedIntegerEntry i j : K) := by
  dsimp only [permutedSixOutputThreeTailSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,permutedSixOutputThreeTailSelectedIntegerEntry]
  rw [permutedSixOutputThreeTailWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] permutedSixOutputThreeTailSelectedIntegerEntry permutedSixOutputThreeTailSelectedData

private theorem selected_integer_entries (i j : Fin 30) :
    permutedSixOutputThreeTailSelectedIntegerEntry i j%101=(permutedSixOutputThreeTailSelectedData i j : ℤ) := by
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

theorem permutedSixOutputThreeTail_selected_integer_binding {K : Type*} [Field K] :
    permutedSixOutputThreeTailSelectedCoefficient (K:=K)=
      Matrix.map permutedSixOutputThreeTailSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem permutedSixOutputThreeTail_selected_binding :
    permutedSixOutputThreeTailSelectedCoefficient (K:=ZMod 101)=permutedSixOutputThreeTailSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (permutedSixOutputThreeTailSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,permutedSixOutputThreeTailSelected] using h2

end FD56
