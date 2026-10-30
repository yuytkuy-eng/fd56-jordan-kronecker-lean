/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedPolynomial
import FD56.Hilbert.SixOutputTenSeedRank

/-! Integral binding of the lower-degree selected coefficient matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sixOutputTenSeedCoefficientRows (i:Fin 45) : Fin 15 × ℕ :=
  let r := (finProdFinEquiv : Fin 15 × Fin 13 ≃ Fin 195).symm (sixOutputTenSeedSelectedRows i)
  (r.1,r.2.val)

def sixOutputTenSeedSelectedIntegerEntry (i j:Fin 45) : ℤ :=
  let r := sixOutputTenSeedCoefficientRows i
  let c := (finProdFinEquiv : Fin 15 × Fin 3 ≃ Fin 45).symm j
  if c.2.val≤r.2 then (sixOutputTenSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputTenSeedSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 45) (Fin 45) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputTenSeedWitness (R:=K)) 2
    sixOutputTenSeedCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 15 × Fin 3 ≃ Fin 45).symm

attribute [local irreducible] sixOutputTenSeedCoefficientRows sixOutputTenSeedPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 45) :
    sixOutputTenSeedSelectedCoefficient (K:=K) i j=(sixOutputTenSeedSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputTenSeedSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputTenSeedSelectedIntegerEntry]
  rw [sixOutputTenSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 0 j%101=(sixOutputTenSeedSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 1 j%101=(sixOutputTenSeedSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 2 j%101=(sixOutputTenSeedSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 3 j%101=(sixOutputTenSeedSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 4 j%101=(sixOutputTenSeedSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 5 j%101=(sixOutputTenSeedSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 6 j%101=(sixOutputTenSeedSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 7 j%101=(sixOutputTenSeedSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 8 j%101=(sixOutputTenSeedSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 9 j%101=(sixOutputTenSeedSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 10 j%101=(sixOutputTenSeedSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 11 j%101=(sixOutputTenSeedSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 12 j%101=(sixOutputTenSeedSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 13 j%101=(sixOutputTenSeedSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 14 j%101=(sixOutputTenSeedSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 15 j%101=(sixOutputTenSeedSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 16 j%101=(sixOutputTenSeedSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 17 j%101=(sixOutputTenSeedSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 18 j%101=(sixOutputTenSeedSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 19 j%101=(sixOutputTenSeedSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 20 j%101=(sixOutputTenSeedSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 21 j%101=(sixOutputTenSeedSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 22 j%101=(sixOutputTenSeedSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 23 j%101=(sixOutputTenSeedSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 24 j%101=(sixOutputTenSeedSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 25 j%101=(sixOutputTenSeedSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 26 j%101=(sixOutputTenSeedSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 27 j%101=(sixOutputTenSeedSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 28 j%101=(sixOutputTenSeedSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 29 j%101=(sixOutputTenSeedSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 30 j%101=(sixOutputTenSeedSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 31 j%101=(sixOutputTenSeedSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 32 j%101=(sixOutputTenSeedSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 33 j%101=(sixOutputTenSeedSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 34 j%101=(sixOutputTenSeedSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 35 j%101=(sixOutputTenSeedSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 36 j%101=(sixOutputTenSeedSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 37 j%101=(sixOutputTenSeedSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 38 j%101=(sixOutputTenSeedSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 39 j%101=(sixOutputTenSeedSelectedData 39 j : ℤ) := by decide +kernel

private theorem selected_row40 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 40 j%101=(sixOutputTenSeedSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 41 j%101=(sixOutputTenSeedSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 42 j%101=(sixOutputTenSeedSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 43 j%101=(sixOutputTenSeedSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 45,
    sixOutputTenSeedSelectedIntegerEntry 44 j%101=(sixOutputTenSeedSelectedData 44 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedSelectedIntegerEntry sixOutputTenSeedSelectedData

private theorem selected_integer_entries (i j:Fin 45) :
    sixOutputTenSeedSelectedIntegerEntry i j%101=(sixOutputTenSeedSelectedData i j:ℤ) := by
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
  · exact selected_row40 j
  · exact selected_row41 j
  · exact selected_row42 j
  · exact selected_row43 j
  · exact selected_row44 j

theorem sixOutputTenSeed_selected_integer_binding {K : Type*} [Field K] :
    sixOutputTenSeedSelectedCoefficient (K:=K) =
      Matrix.map sixOutputTenSeedSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputTenSeed_selected_binding :
    sixOutputTenSeedSelectedCoefficient (K:=ZMod 101)=sixOutputTenSeedSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputTenSeedSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputTenSeedSelected] using h2

end FD56
