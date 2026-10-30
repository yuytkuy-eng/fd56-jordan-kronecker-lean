/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSeventeenTangentPolynomial
import FD56.Hilbert.BalancedSeventeenTangentRank

/-! Integral binding of the degree3 selected coefficient certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def balancedSeventeenTangentCoefficientRows (i:Fin 40) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 21 ≃ Fin 105).symm (balancedSeventeenTangentSelectedRows i)
  (r.1,r.2.val)

def balancedSeventeenTangentSelectedIntegerEntry (i j:Fin 40) : ℤ :=
  let r := balancedSeventeenTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm j
  if c.2.val≤r.2 then (balancedSeventeenTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def balancedSeventeenTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 40) (Fin 40) K :=
  (selectedPolynomialCoefficientMatrix (balancedSeventeenTangentWitness (R:=K)) 3
    balancedSeventeenTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 4 ≃ Fin 40).symm

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 40) :
    balancedSeventeenTangentSelectedCoefficient (K:=K) i j=(balancedSeventeenTangentSelectedIntegerEntry i j : K) := by
  dsimp only [balancedSeventeenTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedSeventeenTangentSelectedIntegerEntry]
  rw [balancedSeventeenTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedSeventeenTangentSelectedIntegerEntry balancedSeventeenTangentSelectedData

private theorem selected_row0 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 0 j%101=(balancedSeventeenTangentSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 1 j%101=(balancedSeventeenTangentSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 2 j%101=(balancedSeventeenTangentSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 3 j%101=(balancedSeventeenTangentSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 4 j%101=(balancedSeventeenTangentSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 5 j%101=(balancedSeventeenTangentSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 6 j%101=(balancedSeventeenTangentSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 7 j%101=(balancedSeventeenTangentSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 8 j%101=(balancedSeventeenTangentSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 9 j%101=(balancedSeventeenTangentSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 10 j%101=(balancedSeventeenTangentSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 11 j%101=(balancedSeventeenTangentSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 12 j%101=(balancedSeventeenTangentSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 13 j%101=(balancedSeventeenTangentSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 14 j%101=(balancedSeventeenTangentSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 15 j%101=(balancedSeventeenTangentSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 16 j%101=(balancedSeventeenTangentSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 17 j%101=(balancedSeventeenTangentSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 18 j%101=(balancedSeventeenTangentSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 19 j%101=(balancedSeventeenTangentSelectedData 19 j : ℤ) := by decide +kernel

private theorem selected_row20 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 20 j%101=(balancedSeventeenTangentSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 21 j%101=(balancedSeventeenTangentSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 22 j%101=(balancedSeventeenTangentSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 23 j%101=(balancedSeventeenTangentSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 24 j%101=(balancedSeventeenTangentSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 25 j%101=(balancedSeventeenTangentSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 26 j%101=(balancedSeventeenTangentSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 27 j%101=(balancedSeventeenTangentSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 28 j%101=(balancedSeventeenTangentSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 29 j%101=(balancedSeventeenTangentSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 30 j%101=(balancedSeventeenTangentSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 31 j%101=(balancedSeventeenTangentSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 32 j%101=(balancedSeventeenTangentSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 33 j%101=(balancedSeventeenTangentSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 34 j%101=(balancedSeventeenTangentSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 35 j%101=(balancedSeventeenTangentSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 36 j%101=(balancedSeventeenTangentSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 37 j%101=(balancedSeventeenTangentSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 38 j%101=(balancedSeventeenTangentSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 40,
    balancedSeventeenTangentSelectedIntegerEntry 39 j%101=(balancedSeventeenTangentSelectedData 39 j : ℤ) := by decide +kernel

private theorem selected_integer_entries (i j:Fin 40) :
    balancedSeventeenTangentSelectedIntegerEntry i j%101=(balancedSeventeenTangentSelectedData i j:ℤ) := by
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

theorem balancedSeventeenTangent_selected_integer_binding {K : Type*} [Field K] :
    balancedSeventeenTangentSelectedCoefficient (K:=K) =
      Matrix.map balancedSeventeenTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedSeventeenTangent_selected_binding :
    balancedSeventeenTangentSelectedCoefficient (K:=ZMod 101)=balancedSeventeenTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedSeventeenTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedSeventeenTangentSelected] using h2

end FD56
