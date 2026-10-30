/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedBinding
import FD56.Hilbert.SixOutputEightSeedCriticalRank

/-! Integral binding of a selected 42-column critical coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sixOutputEightSeedCriticalCoefficientRows (i : Fin 42) : Fin 15 × ℕ :=
  let r := (finProdFinEquiv : Fin 15 × Fin 11 ≃ Fin 165).symm (sixOutputEightSeedCriticalSelectedRows i)
  (r.1,r.2.val)

def sixOutputEightSeedCriticalSelectedIntegerEntry (i j : Fin 42) : ℤ :=
  let r := sixOutputEightSeedCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 15 × Fin 3 ≃ Fin 45).symm (sixOutputEightSeedCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (sixOutputEightSeedPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def sixOutputEightSeedCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 42) (Fin 42) K :=
  (selectedPolynomialCoefficientMatrix (sixOutputEightSeedWitness (R:=K)) 2
    sixOutputEightSeedCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 15 × Fin 3 ≃ Fin 45).symm (sixOutputEightSeedCriticalCoefficientColumns j))

attribute [local irreducible] sixOutputEightSeedCriticalCoefficientRows sixOutputEightSeedPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 42) :
    sixOutputEightSeedCriticalSelectedCoefficient (K:=K) i j=(sixOutputEightSeedCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputEightSeedCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputEightSeedCriticalSelectedIntegerEntry]
  rw [sixOutputEightSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 0 j%101=(sixOutputEightSeedCriticalSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 1 j%101=(sixOutputEightSeedCriticalSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 2 j%101=(sixOutputEightSeedCriticalSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 3 j%101=(sixOutputEightSeedCriticalSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 4 j%101=(sixOutputEightSeedCriticalSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 5 j%101=(sixOutputEightSeedCriticalSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 6 j%101=(sixOutputEightSeedCriticalSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 7 j%101=(sixOutputEightSeedCriticalSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 8 j%101=(sixOutputEightSeedCriticalSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 9 j%101=(sixOutputEightSeedCriticalSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 10 j%101=(sixOutputEightSeedCriticalSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 11 j%101=(sixOutputEightSeedCriticalSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 12 j%101=(sixOutputEightSeedCriticalSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 13 j%101=(sixOutputEightSeedCriticalSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 14 j%101=(sixOutputEightSeedCriticalSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 15 j%101=(sixOutputEightSeedCriticalSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 16 j%101=(sixOutputEightSeedCriticalSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 17 j%101=(sixOutputEightSeedCriticalSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 18 j%101=(sixOutputEightSeedCriticalSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 19 j%101=(sixOutputEightSeedCriticalSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 20 j%101=(sixOutputEightSeedCriticalSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 21 j%101=(sixOutputEightSeedCriticalSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 22 j%101=(sixOutputEightSeedCriticalSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 23 j%101=(sixOutputEightSeedCriticalSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 24 j%101=(sixOutputEightSeedCriticalSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 25 j%101=(sixOutputEightSeedCriticalSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 26 j%101=(sixOutputEightSeedCriticalSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 27 j%101=(sixOutputEightSeedCriticalSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 28 j%101=(sixOutputEightSeedCriticalSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 29 j%101=(sixOutputEightSeedCriticalSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 30 j%101=(sixOutputEightSeedCriticalSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 31 j%101=(sixOutputEightSeedCriticalSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 32 j%101=(sixOutputEightSeedCriticalSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 33 j%101=(sixOutputEightSeedCriticalSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 34 j%101=(sixOutputEightSeedCriticalSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 35 j%101=(sixOutputEightSeedCriticalSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 36 j%101=(sixOutputEightSeedCriticalSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 37 j%101=(sixOutputEightSeedCriticalSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 38 j%101=(sixOutputEightSeedCriticalSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 39 j%101=(sixOutputEightSeedCriticalSelectedData 39 j : ℤ) := by decide +kernel

private theorem selected_row40 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 40 j%101=(sixOutputEightSeedCriticalSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 42,
    sixOutputEightSeedCriticalSelectedIntegerEntry 41 j%101=(sixOutputEightSeedCriticalSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_integer_entries (i j : Fin 42) :
    sixOutputEightSeedCriticalSelectedIntegerEntry i j%101=(sixOutputEightSeedCriticalSelectedData i j : ℤ) := by
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

theorem sixOutputEightSeedCritical_selected_integer_binding {K : Type*} [Field K] :
    sixOutputEightSeedCriticalSelectedCoefficient (K:=K)=Matrix.map sixOutputEightSeedCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputEightSeedCritical_selected_binding :
    sixOutputEightSeedCriticalSelectedCoefficient (K:=ZMod 101)=sixOutputEightSeedCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputEightSeedCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputEightSeedCriticalSelected] using h2

end FD56
