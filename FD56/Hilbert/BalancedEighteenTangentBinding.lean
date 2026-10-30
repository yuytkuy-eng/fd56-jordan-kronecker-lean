/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentBindingRows0
import FD56.Hilbert.BalancedEighteenTangentBindingRows1
import FD56.Hilbert.BalancedEighteenTangentBindingRows2

/-! Integral binding of the selected degree4 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j:Fin 50) :
    balancedEighteenTangentSelectedCoefficient (K:=K) i j=(balancedEighteenTangentSelectedIntegerEntry i j : K) := by
  dsimp only [balancedEighteenTangentSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedEighteenTangentSelectedIntegerEntry]
  rw [balancedEighteenTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedEighteenTangentSelectedIntegerEntry balancedEighteenTangentSelectedData

private theorem selected_integer_entries (i j : Fin 50) :
    balancedEighteenTangentSelectedIntegerEntry i j%101=(balancedEighteenTangentSelectedData i j : ℤ) := by
  by_cases h0 : i.val<20
  · exact balancedEighteenTangent_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<40
  · exact balancedEighteenTangent_selected_integer_rows_1 i j (by omega) h1
  exact balancedEighteenTangent_selected_integer_rows_2 i j (by omega) i.isLt

theorem balancedEighteenTangent_selected_integer_binding {K : Type*} [Field K] :
    balancedEighteenTangentSelectedCoefficient (K:=K) =
      Matrix.map balancedEighteenTangentSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedEighteenTangent_selected_binding :
    balancedEighteenTangentSelectedCoefficient (K:=ZMod 101)=balancedEighteenTangentSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a:ℤ=>(a:ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedEighteenTangentSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedEighteenTangentSelected] using h2

end FD56
