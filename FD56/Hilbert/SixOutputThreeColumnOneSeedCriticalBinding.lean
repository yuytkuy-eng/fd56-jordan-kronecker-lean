/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnOneSeedBinding
import FD56.Hilbert.SixOutputThreeColumnOneSeedCriticalRank

/-! Exact integral binding of the selected tangent coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sixOutputThreeColumnOneSeedCriticalCoefficientRows (i : Fin 32) : Fin 20 × ℕ :=
  let r := (finProdFinEquiv : Fin 20 × Fin 5 ≃ Fin 100).symm (sixOutputThreeColumnOneSeedCriticalSelectedRows i)
  (r.1,r.2.val)

def sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry (i j : Fin 32) : ℤ :=
  let r := sixOutputThreeColumnOneSeedCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 20 × Fin 2 ≃ Fin 40).symm (sixOutputThreeColumnOneSeedCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (sixOutputThreeColumnOneSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputThreeColumnOneSeedCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 32) (Fin 32) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputThreeColumnOneSeedWitness (R:=K)) 1
    sixOutputThreeColumnOneSeedCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 20 × Fin 2 ≃ Fin 40).symm (sixOutputThreeColumnOneSeedCriticalCoefficientColumns j))

attribute [local irreducible] sixOutputThreeColumnOneSeedCriticalCoefficientRows sixOutputThreeColumnOneSeedPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 32) :
    sixOutputThreeColumnOneSeedCriticalSelectedCoefficient (K:=K) i j=(sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputThreeColumnOneSeedCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry]
  rw [sixOutputThreeColumnOneSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 0 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 1 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 2 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 3 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 4 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 5 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 6 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 7 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 8 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 9 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 10 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 11 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 12 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 13 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 14 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 15 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 16 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 17 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 18 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 19 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 20 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 21 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 22 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 23 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 24 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 25 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 26 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 27 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 28 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 29 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 30 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 32,
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry 31 j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData 31 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry sixOutputThreeColumnOneSeedCriticalSelectedData

private theorem selected_integer_entries (i j : Fin 32) :
    sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnOneSeedCriticalSelectedData i j : ℤ) := by
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

theorem sixOutputThreeColumnOneSeedCritical_selected_integer_binding {K : Type*} [Field K] :
    sixOutputThreeColumnOneSeedCriticalSelectedCoefficient (K:=K)=Matrix.map sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputThreeColumnOneSeedCritical_selected_binding :
    sixOutputThreeColumnOneSeedCriticalSelectedCoefficient (K:=ZMod 101)=sixOutputThreeColumnOneSeedCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputThreeColumnOneSeedCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputThreeColumnOneSeedCriticalSelected] using h2

end FD56
