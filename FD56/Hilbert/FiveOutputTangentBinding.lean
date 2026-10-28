/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FiveOutputTangentWitness
import FD56.LinearAlgebra.SelectedPolynomialCoefficients

/-! Exact binding of the selected finite matrix to the polynomial tangent system. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def fiveOutputTangentCoefficientRows (i:Fin 60) : Fin 5 × ℕ :=
  let r := (finProdFinEquiv : Fin 5 × Fin 27 ≃ Fin 135).symm (fiveOutputTangentSelectedRows i)
  (r.1,r.2.val)

def fiveOutputTangentSelectedIntegerEntry (i j:Fin 60) : ℤ :=
  let r := fiveOutputTangentCoefficientRows i
  let c := (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm j
  if c.2.val≤r.2 then (fiveOutputTangentPolynomialData r.1 c.1).getD (r.2-c.2.val) 0 else 0

def fiveOutputTangentSelectedCoefficient {K : Type*} [Field K] : Matrix (Fin 60) (Fin 60) K :=
  (selectedPolynomialCoefficientMatrix (fiveOutputTangentWitness (R:=K)) 5
    fiveOutputTangentCoefficientRows).submatrix id
      (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 60) :
    fiveOutputTangentSelectedCoefficient (K:=K) i j=(fiveOutputTangentSelectedIntegerEntry i j : K) := by
  dsimp only [fiveOutputTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,fiveOutputTangentSelectedIntegerEntry]
  rw [fiveOutputTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_row0 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 0 j%101=(fiveOutputTangentSelectedData 0 j:ℤ) := by decide +kernel

private theorem selected_row1 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 1 j%101=(fiveOutputTangentSelectedData 1 j:ℤ) := by decide +kernel

private theorem selected_row2 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 2 j%101=(fiveOutputTangentSelectedData 2 j:ℤ) := by decide +kernel

private theorem selected_row3 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 3 j%101=(fiveOutputTangentSelectedData 3 j:ℤ) := by decide +kernel

private theorem selected_row4 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 4 j%101=(fiveOutputTangentSelectedData 4 j:ℤ) := by decide +kernel

private theorem selected_row5 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 5 j%101=(fiveOutputTangentSelectedData 5 j:ℤ) := by decide +kernel

private theorem selected_row6 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 6 j%101=(fiveOutputTangentSelectedData 6 j:ℤ) := by decide +kernel

private theorem selected_row7 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 7 j%101=(fiveOutputTangentSelectedData 7 j:ℤ) := by decide +kernel

private theorem selected_row8 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 8 j%101=(fiveOutputTangentSelectedData 8 j:ℤ) := by decide +kernel

private theorem selected_row9 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 9 j%101=(fiveOutputTangentSelectedData 9 j:ℤ) := by decide +kernel

private theorem selected_row10 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 10 j%101=(fiveOutputTangentSelectedData 10 j:ℤ) := by decide +kernel

private theorem selected_row11 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 11 j%101=(fiveOutputTangentSelectedData 11 j:ℤ) := by decide +kernel

private theorem selected_row12 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 12 j%101=(fiveOutputTangentSelectedData 12 j:ℤ) := by decide +kernel

private theorem selected_row13 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 13 j%101=(fiveOutputTangentSelectedData 13 j:ℤ) := by decide +kernel

private theorem selected_row14 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 14 j%101=(fiveOutputTangentSelectedData 14 j:ℤ) := by decide +kernel

private theorem selected_row15 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 15 j%101=(fiveOutputTangentSelectedData 15 j:ℤ) := by decide +kernel

private theorem selected_row16 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 16 j%101=(fiveOutputTangentSelectedData 16 j:ℤ) := by decide +kernel

private theorem selected_row17 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 17 j%101=(fiveOutputTangentSelectedData 17 j:ℤ) := by decide +kernel

private theorem selected_row18 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 18 j%101=(fiveOutputTangentSelectedData 18 j:ℤ) := by decide +kernel

private theorem selected_row19 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 19 j%101=(fiveOutputTangentSelectedData 19 j:ℤ) := by decide +kernel

private theorem selected_row20 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 20 j%101=(fiveOutputTangentSelectedData 20 j:ℤ) := by decide +kernel

private theorem selected_row21 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 21 j%101=(fiveOutputTangentSelectedData 21 j:ℤ) := by decide +kernel

private theorem selected_row22 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 22 j%101=(fiveOutputTangentSelectedData 22 j:ℤ) := by decide +kernel

private theorem selected_row23 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 23 j%101=(fiveOutputTangentSelectedData 23 j:ℤ) := by decide +kernel

private theorem selected_row24 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 24 j%101=(fiveOutputTangentSelectedData 24 j:ℤ) := by decide +kernel

private theorem selected_row25 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 25 j%101=(fiveOutputTangentSelectedData 25 j:ℤ) := by decide +kernel

private theorem selected_row26 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 26 j%101=(fiveOutputTangentSelectedData 26 j:ℤ) := by decide +kernel

private theorem selected_row27 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 27 j%101=(fiveOutputTangentSelectedData 27 j:ℤ) := by decide +kernel

private theorem selected_row28 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 28 j%101=(fiveOutputTangentSelectedData 28 j:ℤ) := by decide +kernel

private theorem selected_row29 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 29 j%101=(fiveOutputTangentSelectedData 29 j:ℤ) := by decide +kernel

private theorem selected_row30 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 30 j%101=(fiveOutputTangentSelectedData 30 j:ℤ) := by decide +kernel

private theorem selected_row31 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 31 j%101=(fiveOutputTangentSelectedData 31 j:ℤ) := by decide +kernel

private theorem selected_row32 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 32 j%101=(fiveOutputTangentSelectedData 32 j:ℤ) := by decide +kernel

private theorem selected_row33 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 33 j%101=(fiveOutputTangentSelectedData 33 j:ℤ) := by decide +kernel

private theorem selected_row34 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 34 j%101=(fiveOutputTangentSelectedData 34 j:ℤ) := by decide +kernel

private theorem selected_row35 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 35 j%101=(fiveOutputTangentSelectedData 35 j:ℤ) := by decide +kernel

private theorem selected_row36 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 36 j%101=(fiveOutputTangentSelectedData 36 j:ℤ) := by decide +kernel

private theorem selected_row37 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 37 j%101=(fiveOutputTangentSelectedData 37 j:ℤ) := by decide +kernel

private theorem selected_row38 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 38 j%101=(fiveOutputTangentSelectedData 38 j:ℤ) := by decide +kernel

private theorem selected_row39 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 39 j%101=(fiveOutputTangentSelectedData 39 j:ℤ) := by decide +kernel

private theorem selected_row40 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 40 j%101=(fiveOutputTangentSelectedData 40 j:ℤ) := by decide +kernel

private theorem selected_row41 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 41 j%101=(fiveOutputTangentSelectedData 41 j:ℤ) := by decide +kernel

private theorem selected_row42 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 42 j%101=(fiveOutputTangentSelectedData 42 j:ℤ) := by decide +kernel

private theorem selected_row43 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 43 j%101=(fiveOutputTangentSelectedData 43 j:ℤ) := by decide +kernel

private theorem selected_row44 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 44 j%101=(fiveOutputTangentSelectedData 44 j:ℤ) := by decide +kernel

private theorem selected_row45 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 45 j%101=(fiveOutputTangentSelectedData 45 j:ℤ) := by decide +kernel

private theorem selected_row46 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 46 j%101=(fiveOutputTangentSelectedData 46 j:ℤ) := by decide +kernel

private theorem selected_row47 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 47 j%101=(fiveOutputTangentSelectedData 47 j:ℤ) := by decide +kernel

private theorem selected_row48 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 48 j%101=(fiveOutputTangentSelectedData 48 j:ℤ) := by decide +kernel

private theorem selected_row49 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 49 j%101=(fiveOutputTangentSelectedData 49 j:ℤ) := by decide +kernel

private theorem selected_row50 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 50 j%101=(fiveOutputTangentSelectedData 50 j:ℤ) := by decide +kernel

private theorem selected_row51 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 51 j%101=(fiveOutputTangentSelectedData 51 j:ℤ) := by decide +kernel

private theorem selected_row52 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 52 j%101=(fiveOutputTangentSelectedData 52 j:ℤ) := by decide +kernel

private theorem selected_row53 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 53 j%101=(fiveOutputTangentSelectedData 53 j:ℤ) := by decide +kernel

private theorem selected_row54 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 54 j%101=(fiveOutputTangentSelectedData 54 j:ℤ) := by decide +kernel

private theorem selected_row55 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 55 j%101=(fiveOutputTangentSelectedData 55 j:ℤ) := by decide +kernel

private theorem selected_row56 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 56 j%101=(fiveOutputTangentSelectedData 56 j:ℤ) := by decide +kernel

private theorem selected_row57 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 57 j%101=(fiveOutputTangentSelectedData 57 j:ℤ) := by decide +kernel

private theorem selected_row58 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 58 j%101=(fiveOutputTangentSelectedData 58 j:ℤ) := by decide +kernel

private theorem selected_row59 : ∀j:Fin 60,
    fiveOutputTangentSelectedIntegerEntry 59 j%101=(fiveOutputTangentSelectedData 59 j:ℤ) := by decide +kernel

attribute [local irreducible] fiveOutputTangentSelectedIntegerEntry fiveOutputTangentSelectedData

private theorem selected_integer_entries (i j:Fin 60) :
    fiveOutputTangentSelectedIntegerEntry i j%101=(fiveOutputTangentSelectedData i j:ℤ) := by
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
  · exact selected_row49 j
  · exact selected_row50 j
  · exact selected_row51 j
  · exact selected_row52 j
  · exact selected_row53 j
  · exact selected_row54 j
  · exact selected_row55 j
  · exact selected_row56 j
  · exact selected_row57 j
  · exact selected_row58 j
  · exact selected_row59 j

theorem fiveOutputTangent_selected_integer_binding {K : Type*} [Field K] :
    fiveOutputTangentSelectedCoefficient (K:=K) =
      Matrix.map fiveOutputTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem fiveOutputTangent_selected_binding :
    fiveOutputTangentSelectedCoefficient (K:=ZMod 101)=fiveOutputTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (fiveOutputTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,fiveOutputTangentSelected] using h2

end FD56
