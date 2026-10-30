/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingRows0
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingRows1
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingRows2
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingRows3
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingRows4
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingRows5
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingRows6

/-! Integral binding of the selected degree6 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 69) :
    balancedTwentyFourTangentCriticalSelectedCoefficient (K:=K) i j=(balancedTwentyFourTangentCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [balancedTwentyFourTangentCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedTwentyFourTangentCriticalSelectedIntegerEntry]
  rw [balancedTwentyFourTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedTwentyFourTangentCriticalSelectedIntegerEntry balancedTwentyFourTangentCriticalSelectedData

private theorem selected_integer_entries (i j : Fin 69) :
    balancedTwentyFourTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFourTangentCriticalSelectedData i j : ℤ) := by
  by_cases h0 : i.val<10
  · exact balancedTwentyFourTangentCritical_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyFourTangentCritical_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyFourTangentCritical_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyFourTangentCritical_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyFourTangentCritical_selected_integer_rows_4 i j (by omega) h4
  by_cases h5 : i.val<60
  · exact balancedTwentyFourTangentCritical_selected_integer_rows_5 i j (by omega) h5
  exact balancedTwentyFourTangentCritical_selected_integer_rows_6 i j (by omega) i.isLt

theorem balancedTwentyFourTangentCritical_selected_integer_binding {K : Type*} [Field K] :
    balancedTwentyFourTangentCriticalSelectedCoefficient (K:=K)=Matrix.map balancedTwentyFourTangentCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedTwentyFourTangentCritical_selected_binding :
    balancedTwentyFourTangentCriticalSelectedCoefficient (K:=ZMod 101)=balancedTwentyFourTangentCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedTwentyFourTangentCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedTwentyFourTangentCriticalSelected] using h2

end FD56
