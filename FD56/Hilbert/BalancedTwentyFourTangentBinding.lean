/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentBindingRows0
import FD56.Hilbert.BalancedTwentyFourTangentBindingRows1
import FD56.Hilbert.BalancedTwentyFourTangentBindingRows2
import FD56.Hilbert.BalancedTwentyFourTangentBindingRows3
import FD56.Hilbert.BalancedTwentyFourTangentBindingRows4
import FD56.Hilbert.BalancedTwentyFourTangentBindingRows5

/-! Integral binding of the selected degree5 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 60) :
    balancedTwentyFourTangentSelectedCoefficient (K:=K) i j=(balancedTwentyFourTangentSelectedIntegerEntry i j : K) := by
  dsimp only [balancedTwentyFourTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedTwentyFourTangentSelectedIntegerEntry]
  rw [balancedTwentyFourTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedTwentyFourTangentSelectedIntegerEntry balancedTwentyFourTangentSelectedData

private theorem selected_integer_entries (i j : Fin 60) :
    balancedTwentyFourTangentSelectedIntegerEntry i j%101=(balancedTwentyFourTangentSelectedData i j : ℤ) := by
  by_cases h0 : i.val<10
  · exact balancedTwentyFourTangent_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyFourTangent_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyFourTangent_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyFourTangent_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyFourTangent_selected_integer_rows_4 i j (by omega) h4
  exact balancedTwentyFourTangent_selected_integer_rows_5 i j (by omega) i.isLt

theorem balancedTwentyFourTangent_selected_integer_binding {K : Type*} [Field K] :
    balancedTwentyFourTangentSelectedCoefficient (K:=K) =
      Matrix.map balancedTwentyFourTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedTwentyFourTangent_selected_binding :
    balancedTwentyFourTangentSelectedCoefficient (K:=ZMod 101)=balancedTwentyFourTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedTwentyFourTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedTwentyFourTangentSelected] using h2

end FD56
