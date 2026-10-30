/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnOneSeedPolynomial
import FD56.Hilbert.SixOutputThreeColumnOneSeedRank

/-! Exact integral binding of the selected tangent coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sixOutputThreeColumnOneSeedCoefficientRows (i:Fin 20) : Fin 20 × ℕ :=
  let r := (finProdFinEquiv : Fin 20 × Fin 4 ≃ Fin 80).symm (sixOutputThreeColumnOneSeedSelectedRows i)
  (r.1,r.2.val)

def sixOutputThreeColumnOneSeedSelectedIntegerEntry (i j:Fin 20) : ℤ :=
  let r := sixOutputThreeColumnOneSeedCoefficientRows i
  let c := (finProdFinEquiv : Fin 20 × Fin 1 ≃ Fin 20).symm j
  if c.2.val≤r.2 then (sixOutputThreeColumnOneSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputThreeColumnOneSeedSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 20) (Fin 20) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputThreeColumnOneSeedWitness (R:=K)) 0
    sixOutputThreeColumnOneSeedCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 20 × Fin 1 ≃ Fin 20).symm

attribute [local irreducible] sixOutputThreeColumnOneSeedCoefficientRows sixOutputThreeColumnOneSeedPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 20) :
    sixOutputThreeColumnOneSeedSelectedCoefficient (K:=K) i j=(sixOutputThreeColumnOneSeedSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputThreeColumnOneSeedSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputThreeColumnOneSeedSelectedIntegerEntry]
  rw [sixOutputThreeColumnOneSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 0 j%101=(sixOutputThreeColumnOneSeedSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 1 j%101=(sixOutputThreeColumnOneSeedSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 2 j%101=(sixOutputThreeColumnOneSeedSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 3 j%101=(sixOutputThreeColumnOneSeedSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 4 j%101=(sixOutputThreeColumnOneSeedSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 5 j%101=(sixOutputThreeColumnOneSeedSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 6 j%101=(sixOutputThreeColumnOneSeedSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 7 j%101=(sixOutputThreeColumnOneSeedSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 8 j%101=(sixOutputThreeColumnOneSeedSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 9 j%101=(sixOutputThreeColumnOneSeedSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 10 j%101=(sixOutputThreeColumnOneSeedSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 11 j%101=(sixOutputThreeColumnOneSeedSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 12 j%101=(sixOutputThreeColumnOneSeedSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 13 j%101=(sixOutputThreeColumnOneSeedSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 14 j%101=(sixOutputThreeColumnOneSeedSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 15 j%101=(sixOutputThreeColumnOneSeedSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 16 j%101=(sixOutputThreeColumnOneSeedSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 17 j%101=(sixOutputThreeColumnOneSeedSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 18 j%101=(sixOutputThreeColumnOneSeedSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 20,
    sixOutputThreeColumnOneSeedSelectedIntegerEntry 19 j%101=(sixOutputThreeColumnOneSeedSelectedData 19 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnOneSeedSelectedIntegerEntry sixOutputThreeColumnOneSeedSelectedData

private theorem selected_integer_entries (i j:Fin 20) :
    sixOutputThreeColumnOneSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnOneSeedSelectedData i j:ℤ) := by
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

theorem sixOutputThreeColumnOneSeed_selected_integer_binding {K : Type*} [Field K] :
    sixOutputThreeColumnOneSeedSelectedCoefficient (K:=K) =
      Matrix.map sixOutputThreeColumnOneSeedSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputThreeColumnOneSeed_selected_binding :
    sixOutputThreeColumnOneSeedSelectedCoefficient (K:=ZMod 101)=sixOutputThreeColumnOneSeedSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputThreeColumnOneSeedSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputThreeColumnOneSeedSelected] using h2

end FD56
