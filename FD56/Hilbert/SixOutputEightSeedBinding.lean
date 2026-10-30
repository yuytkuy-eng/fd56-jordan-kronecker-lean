/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedPolynomial
import FD56.Hilbert.SixOutputEightSeedRank

/-! Integral binding of the lower-degree selected coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sixOutputEightSeedCoefficientRows (i:Fin 30) : Fin 15 × ℕ :=
  let r := (finProdFinEquiv : Fin 15 × Fin 10 ≃ Fin 150).symm (sixOutputEightSeedSelectedRows i)
  (r.1,r.2.val)

def sixOutputEightSeedSelectedIntegerEntry (i j:Fin 30) : ℤ :=
  let r := sixOutputEightSeedCoefficientRows i
  let c := (finProdFinEquiv : Fin 15 × Fin 2 ≃ Fin 30).symm j
  if c.2.val≤r.2 then (sixOutputEightSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputEightSeedSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 30) (Fin 30) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputEightSeedWitness (R:=K)) 1
    sixOutputEightSeedCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 15 × Fin 2 ≃ Fin 30).symm

attribute [local irreducible] sixOutputEightSeedCoefficientRows sixOutputEightSeedPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 30) :
    sixOutputEightSeedSelectedCoefficient (K:=K) i j=(sixOutputEightSeedSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputEightSeedSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputEightSeedSelectedIntegerEntry]
  rw [sixOutputEightSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 0 j%101=(sixOutputEightSeedSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 1 j%101=(sixOutputEightSeedSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 2 j%101=(sixOutputEightSeedSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 3 j%101=(sixOutputEightSeedSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 4 j%101=(sixOutputEightSeedSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 5 j%101=(sixOutputEightSeedSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 6 j%101=(sixOutputEightSeedSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 7 j%101=(sixOutputEightSeedSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 8 j%101=(sixOutputEightSeedSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 9 j%101=(sixOutputEightSeedSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 10 j%101=(sixOutputEightSeedSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 11 j%101=(sixOutputEightSeedSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 12 j%101=(sixOutputEightSeedSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 13 j%101=(sixOutputEightSeedSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 14 j%101=(sixOutputEightSeedSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 15 j%101=(sixOutputEightSeedSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 16 j%101=(sixOutputEightSeedSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 17 j%101=(sixOutputEightSeedSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 18 j%101=(sixOutputEightSeedSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 19 j%101=(sixOutputEightSeedSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 20 j%101=(sixOutputEightSeedSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 21 j%101=(sixOutputEightSeedSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 22 j%101=(sixOutputEightSeedSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 23 j%101=(sixOutputEightSeedSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 24 j%101=(sixOutputEightSeedSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 25 j%101=(sixOutputEightSeedSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 26 j%101=(sixOutputEightSeedSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 27 j%101=(sixOutputEightSeedSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 28 j%101=(sixOutputEightSeedSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 30,
    sixOutputEightSeedSelectedIntegerEntry 29 j%101=(sixOutputEightSeedSelectedData 29 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputEightSeedSelectedIntegerEntry sixOutputEightSeedSelectedData

private theorem selected_integer_entries (i j:Fin 30) :
    sixOutputEightSeedSelectedIntegerEntry i j%101=(sixOutputEightSeedSelectedData i j:ℤ) := by
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

theorem sixOutputEightSeed_selected_integer_binding {K : Type*} [Field K] :
    sixOutputEightSeedSelectedCoefficient (K:=K) =
      Matrix.map sixOutputEightSeedSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputEightSeed_selected_binding :
    sixOutputEightSeedSelectedCoefficient (K:=ZMod 101)=sixOutputEightSeedSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputEightSeedSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputEightSeedSelected] using h2

end FD56
