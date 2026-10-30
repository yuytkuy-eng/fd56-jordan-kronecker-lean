/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSeventeenTangentBinding
import FD56.Hilbert.BalancedSeventeenTangentCriticalRank

/-! The selected49-column degree4 coefficient minor is integral. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedSeventeenTangentCriticalCoefficientRows (i : Fin 49) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 22 ≃ Fin 110).symm (balancedSeventeenTangentCriticalSelectedRows i)
  (r.1,r.2.val)

def balancedSeventeenTangentCriticalSelectedIntegerEntry (i j : Fin 49) : ℤ :=
  let r := balancedSeventeenTangentCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm (balancedSeventeenTangentCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (balancedSeventeenTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedSeventeenTangentCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 49) (Fin 49) K :=
  (selectedPolynomialCoefficientMatrix (balancedSeventeenTangentWitness (R:=K)) 4
    balancedSeventeenTangentCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm (balancedSeventeenTangentCriticalCoefficientColumns j))

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 49) :
    balancedSeventeenTangentCriticalSelectedCoefficient (K:=K) i j=(balancedSeventeenTangentCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [balancedSeventeenTangentCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedSeventeenTangentCriticalSelectedIntegerEntry]
  rw [balancedSeventeenTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 0 j%101=(balancedSeventeenTangentCriticalSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 1 j%101=(balancedSeventeenTangentCriticalSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 2 j%101=(balancedSeventeenTangentCriticalSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 3 j%101=(balancedSeventeenTangentCriticalSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 4 j%101=(balancedSeventeenTangentCriticalSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 5 j%101=(balancedSeventeenTangentCriticalSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 6 j%101=(balancedSeventeenTangentCriticalSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 7 j%101=(balancedSeventeenTangentCriticalSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 8 j%101=(balancedSeventeenTangentCriticalSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 9 j%101=(balancedSeventeenTangentCriticalSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 10 j%101=(balancedSeventeenTangentCriticalSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 11 j%101=(balancedSeventeenTangentCriticalSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 12 j%101=(balancedSeventeenTangentCriticalSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 13 j%101=(balancedSeventeenTangentCriticalSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 14 j%101=(balancedSeventeenTangentCriticalSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 15 j%101=(balancedSeventeenTangentCriticalSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 16 j%101=(balancedSeventeenTangentCriticalSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 17 j%101=(balancedSeventeenTangentCriticalSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 18 j%101=(balancedSeventeenTangentCriticalSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 19 j%101=(balancedSeventeenTangentCriticalSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 20 j%101=(balancedSeventeenTangentCriticalSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 21 j%101=(balancedSeventeenTangentCriticalSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 22 j%101=(balancedSeventeenTangentCriticalSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 23 j%101=(balancedSeventeenTangentCriticalSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 24 j%101=(balancedSeventeenTangentCriticalSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 25 j%101=(balancedSeventeenTangentCriticalSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 26 j%101=(balancedSeventeenTangentCriticalSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 27 j%101=(balancedSeventeenTangentCriticalSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 28 j%101=(balancedSeventeenTangentCriticalSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 29 j%101=(balancedSeventeenTangentCriticalSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 30 j%101=(balancedSeventeenTangentCriticalSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 31 j%101=(balancedSeventeenTangentCriticalSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 32 j%101=(balancedSeventeenTangentCriticalSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 33 j%101=(balancedSeventeenTangentCriticalSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 34 j%101=(balancedSeventeenTangentCriticalSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 35 j%101=(balancedSeventeenTangentCriticalSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 36 j%101=(balancedSeventeenTangentCriticalSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 37 j%101=(balancedSeventeenTangentCriticalSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 38 j%101=(balancedSeventeenTangentCriticalSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 39 j%101=(balancedSeventeenTangentCriticalSelectedData 39 j : ℤ) := by decide +kernel

private theorem selected_row40 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 40 j%101=(balancedSeventeenTangentCriticalSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 41 j%101=(balancedSeventeenTangentCriticalSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 42 j%101=(balancedSeventeenTangentCriticalSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 43 j%101=(balancedSeventeenTangentCriticalSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 44 j%101=(balancedSeventeenTangentCriticalSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 45 j%101=(balancedSeventeenTangentCriticalSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 46 j%101=(balancedSeventeenTangentCriticalSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 47 j%101=(balancedSeventeenTangentCriticalSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 49,
    balancedSeventeenTangentCriticalSelectedIntegerEntry 48 j%101=(balancedSeventeenTangentCriticalSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_integer_entries (i j : Fin 49) :
    balancedSeventeenTangentCriticalSelectedIntegerEntry i j%101=(balancedSeventeenTangentCriticalSelectedData i j : ℤ) := by
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
  · exact selected_row45 j
  · exact selected_row46 j
  · exact selected_row47 j
  · exact selected_row48 j

theorem balancedSeventeenTangentCritical_selected_integer_binding {K : Type*} [Field K] :
    balancedSeventeenTangentCriticalSelectedCoefficient (K:=K)=Matrix.map balancedSeventeenTangentCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedSeventeenTangentCritical_selected_binding :
    balancedSeventeenTangentCriticalSelectedCoefficient (K:=ZMod 101)=balancedSeventeenTangentCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedSeventeenTangentCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedSeventeenTangentCriticalSelected] using h2

end FD56
