/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSixteenTangentBinding
import FD56.Hilbert.BalancedSixteenTangentCriticalRank

/-! The selected47-column degree-four coefficient minor is integral. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedSixteenTangentCriticalCoefficientRows (i : Fin 47) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 21 ≃ Fin 105).symm (balancedSixteenTangentCriticalSelectedRows i)
  (r.1,r.2.val)

def balancedSixteenTangentCriticalSelectedIntegerEntry (i j : Fin 47) : ℤ :=
  let r := balancedSixteenTangentCriticalCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm (balancedSixteenTangentCriticalCoefficientColumns j)
  if c.2.val≤r.2 then (balancedSixteenTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedSixteenTangentCriticalSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 47) (Fin 47) K :=
  (selectedPolynomialCoefficientMatrix (balancedSixteenTangentWitness (R:=K)) 4
    balancedSixteenTangentCriticalCoefficientRows).submatrix id
      (fun j => (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm (balancedSixteenTangentCriticalCoefficientColumns j))

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 47) :
    balancedSixteenTangentCriticalSelectedCoefficient (K:=K) i j=(balancedSixteenTangentCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [balancedSixteenTangentCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedSixteenTangentCriticalSelectedIntegerEntry]
  rw [balancedSixteenTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 0 j%101=(balancedSixteenTangentCriticalSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 1 j%101=(balancedSixteenTangentCriticalSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 2 j%101=(balancedSixteenTangentCriticalSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 3 j%101=(balancedSixteenTangentCriticalSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 4 j%101=(balancedSixteenTangentCriticalSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 5 j%101=(balancedSixteenTangentCriticalSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 6 j%101=(balancedSixteenTangentCriticalSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 7 j%101=(balancedSixteenTangentCriticalSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 8 j%101=(balancedSixteenTangentCriticalSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 9 j%101=(balancedSixteenTangentCriticalSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 10 j%101=(balancedSixteenTangentCriticalSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 11 j%101=(balancedSixteenTangentCriticalSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 12 j%101=(balancedSixteenTangentCriticalSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 13 j%101=(balancedSixteenTangentCriticalSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 14 j%101=(balancedSixteenTangentCriticalSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 15 j%101=(balancedSixteenTangentCriticalSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 16 j%101=(balancedSixteenTangentCriticalSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 17 j%101=(balancedSixteenTangentCriticalSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 18 j%101=(balancedSixteenTangentCriticalSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 19 j%101=(balancedSixteenTangentCriticalSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 20 j%101=(balancedSixteenTangentCriticalSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 21 j%101=(balancedSixteenTangentCriticalSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 22 j%101=(balancedSixteenTangentCriticalSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 23 j%101=(balancedSixteenTangentCriticalSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 24 j%101=(balancedSixteenTangentCriticalSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 25 j%101=(balancedSixteenTangentCriticalSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 26 j%101=(balancedSixteenTangentCriticalSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 27 j%101=(balancedSixteenTangentCriticalSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 28 j%101=(balancedSixteenTangentCriticalSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 29 j%101=(balancedSixteenTangentCriticalSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 30 j%101=(balancedSixteenTangentCriticalSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 31 j%101=(balancedSixteenTangentCriticalSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 32 j%101=(balancedSixteenTangentCriticalSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 33 j%101=(balancedSixteenTangentCriticalSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 34 j%101=(balancedSixteenTangentCriticalSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 35 j%101=(balancedSixteenTangentCriticalSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 36 j%101=(balancedSixteenTangentCriticalSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 37 j%101=(balancedSixteenTangentCriticalSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 38 j%101=(balancedSixteenTangentCriticalSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 39 j%101=(balancedSixteenTangentCriticalSelectedData 39 j : ℤ) := by decide +kernel

private theorem selected_row40 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 40 j%101=(balancedSixteenTangentCriticalSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 41 j%101=(balancedSixteenTangentCriticalSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 42 j%101=(balancedSixteenTangentCriticalSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 43 j%101=(balancedSixteenTangentCriticalSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 44 j%101=(balancedSixteenTangentCriticalSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 45 j%101=(balancedSixteenTangentCriticalSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 47,
    balancedSixteenTangentCriticalSelectedIntegerEntry 46 j%101=(balancedSixteenTangentCriticalSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_integer_entries (i j : Fin 47) :
    balancedSixteenTangentCriticalSelectedIntegerEntry i j%101=(balancedSixteenTangentCriticalSelectedData i j : ℤ) := by
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

theorem balancedSixteenTangentCritical_selected_integer_binding {K : Type*} [Field K] :
    balancedSixteenTangentCriticalSelectedCoefficient (K:=K)=Matrix.map balancedSixteenTangentCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedSixteenTangentCritical_selected_binding :
    balancedSixteenTangentCriticalSelectedCoefficient (K:=ZMod 101)=balancedSixteenTangentCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedSixteenTangentCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedSixteenTangentCriticalSelected] using h2

end FD56
