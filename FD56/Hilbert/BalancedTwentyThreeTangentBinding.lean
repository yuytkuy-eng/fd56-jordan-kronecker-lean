/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentBindingRows0
import FD56.Hilbert.BalancedTwentyThreeTangentBindingRows1
import FD56.Hilbert.BalancedTwentyThreeTangentBindingRows2
import FD56.Hilbert.BalancedTwentyThreeTangentBindingRows3
import FD56.Hilbert.BalancedTwentyThreeTangentBindingRows4
import FD56.Hilbert.BalancedTwentyThreeTangentBindingRows5

/-! Integral binding of the selected degree5 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 60) :
    balancedTwentyThreeTangentSelectedCoefficient (K:=K) i j=(balancedTwentyThreeTangentSelectedIntegerEntry i j : K) := by
  dsimp only [balancedTwentyThreeTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedTwentyThreeTangentSelectedIntegerEntry]
  rw [balancedTwentyThreeTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedTwentyThreeTangentSelectedIntegerEntry balancedTwentyThreeTangentSelectedData

private theorem selected_integer_entries (i j : Fin 60) :
    balancedTwentyThreeTangentSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentSelectedData i j : ℤ) := by
  by_cases h0 : i.val<10
  · exact balancedTwentyThreeTangent_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyThreeTangent_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyThreeTangent_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyThreeTangent_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyThreeTangent_selected_integer_rows_4 i j (by omega) h4
  exact balancedTwentyThreeTangent_selected_integer_rows_5 i j (by omega) i.isLt

theorem balancedTwentyThreeTangent_selected_integer_binding {K : Type*} [Field K] :
    balancedTwentyThreeTangentSelectedCoefficient (K:=K) =
      Matrix.map balancedTwentyThreeTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedTwentyThreeTangent_selected_binding :
    balancedTwentyThreeTangentSelectedCoefficient (K:=ZMod 101)=balancedTwentyThreeTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedTwentyThreeTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedTwentyThreeTangentSelected] using h2

end FD56
