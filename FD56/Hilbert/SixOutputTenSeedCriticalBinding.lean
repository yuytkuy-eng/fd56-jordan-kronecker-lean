/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedCriticalBindingRows0
import FD56.Hilbert.SixOutputTenSeedCriticalBindingRows1
import FD56.Hilbert.SixOutputTenSeedCriticalBindingRows2
import FD56.Hilbert.SixOutputTenSeedCriticalBindingRows3
import FD56.Hilbert.SixOutputTenSeedCriticalBindingRows4
import FD56.Hilbert.SixOutputTenSeedCriticalBindingRows5

/-! Integral binding of the selected degree3 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 54) :
    sixOutputTenSeedCriticalSelectedCoefficient (K:=K) i j=(sixOutputTenSeedCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputTenSeedCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputTenSeedCriticalSelectedIntegerEntry]
  rw [sixOutputTenSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] sixOutputTenSeedCriticalSelectedIntegerEntry sixOutputTenSeedCriticalSelectedData

private theorem selected_integer_entries (i j : Fin 54) :
    sixOutputTenSeedCriticalSelectedIntegerEntry i j%101=(sixOutputTenSeedCriticalSelectedData i j : ℤ) := by
  by_cases h0 : i.val<10
  · exact sixOutputTenSeedCritical_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact sixOutputTenSeedCritical_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact sixOutputTenSeedCritical_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact sixOutputTenSeedCritical_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact sixOutputTenSeedCritical_selected_integer_rows_4 i j (by omega) h4
  exact sixOutputTenSeedCritical_selected_integer_rows_5 i j (by omega) i.isLt

theorem sixOutputTenSeedCritical_selected_integer_binding {K : Type*} [Field K] :
    sixOutputTenSeedCriticalSelectedCoefficient (K:=K)=Matrix.map sixOutputTenSeedCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputTenSeedCritical_selected_binding :
    sixOutputTenSeedCriticalSelectedCoefficient (K:=ZMod 101)=sixOutputTenSeedCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputTenSeedCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputTenSeedCriticalSelected] using h2

end FD56
