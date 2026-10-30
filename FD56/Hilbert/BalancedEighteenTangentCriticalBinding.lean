/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentCriticalBindingRows0
import FD56.Hilbert.BalancedEighteenTangentCriticalBindingRows1
import FD56.Hilbert.BalancedEighteenTangentCriticalBindingRows2

/-! Integral binding of the selected degree5 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 54) :
    balancedEighteenTangentCriticalSelectedCoefficient (K:=K) i j=(balancedEighteenTangentCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [balancedEighteenTangentCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedEighteenTangentCriticalSelectedIntegerEntry]
  rw [balancedEighteenTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedEighteenTangentCriticalSelectedIntegerEntry balancedEighteenTangentCriticalSelectedData

private theorem selected_integer_entries (i j : Fin 54) :
    balancedEighteenTangentCriticalSelectedIntegerEntry i j%101=(balancedEighteenTangentCriticalSelectedData i j : ℤ) := by
  by_cases h0 : i.val<20
  · exact balancedEighteenTangentCritical_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<40
  · exact balancedEighteenTangentCritical_selected_integer_rows_1 i j (by omega) h1
  exact balancedEighteenTangentCritical_selected_integer_rows_2 i j (by omega) i.isLt

theorem balancedEighteenTangentCritical_selected_integer_binding {K : Type*} [Field K] :
    balancedEighteenTangentCriticalSelectedCoefficient (K:=K)=Matrix.map balancedEighteenTangentCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedEighteenTangentCritical_selected_binding :
    balancedEighteenTangentCriticalSelectedCoefficient (K:=ZMod 101)=balancedEighteenTangentCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedEighteenTangentCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedEighteenTangentCriticalSelected] using h2

end FD56
