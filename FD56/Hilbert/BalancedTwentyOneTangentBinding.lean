/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentBindingRows0
import FD56.Hilbert.BalancedTwentyOneTangentBindingRows1
import FD56.Hilbert.BalancedTwentyOneTangentBindingRows2

/-! Integral binding of the selected degree5 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 60) :
    balancedTwentyOneTangentSelectedCoefficient (K:=K) i j=(balancedTwentyOneTangentSelectedIntegerEntry i j : K) := by
  dsimp only [balancedTwentyOneTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedTwentyOneTangentSelectedIntegerEntry]
  rw [balancedTwentyOneTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedTwentyOneTangentSelectedIntegerEntry balancedTwentyOneTangentSelectedData

private theorem selected_integer_entries (i j : Fin 60) :
    balancedTwentyOneTangentSelectedIntegerEntry i j%101=(balancedTwentyOneTangentSelectedData i j : ℤ) := by
  by_cases h0 : i.val<20
  · exact balancedTwentyOneTangent_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<40
  · exact balancedTwentyOneTangent_selected_integer_rows_1 i j (by omega) h1
  exact balancedTwentyOneTangent_selected_integer_rows_2 i j (by omega) i.isLt

theorem balancedTwentyOneTangent_selected_integer_binding {K : Type*} [Field K] :
    balancedTwentyOneTangentSelectedCoefficient (K:=K) =
      Matrix.map balancedTwentyOneTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedTwentyOneTangent_selected_binding :
    balancedTwentyOneTangentSelectedCoefficient (K:=ZMod 101)=balancedTwentyOneTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedTwentyOneTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedTwentyOneTangentSelected] using h2

end FD56
