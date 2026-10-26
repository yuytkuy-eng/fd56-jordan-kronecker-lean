/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Invertible changes of independent matrix-column variables. -/

noncomputable section
namespace FD56
open Matrix MvPolynomial
open scoped BigOperators
variable {K n m : Type*} [CommRing K] [Fintype n] [DecidableEq n]

def outputVariableChangeHom (S : Matrix n n K) :
    MvPolynomial (m × n) K →+* MvPolynomial (m × n) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun aj => ∑ k, MvPolynomial.X (aj.1,k) * MvPolynomial.C (S k aj.2))

omit [DecidableEq n] in
theorem outputVariableChangeHom_X (S : Matrix n n K) (a : m) (j : n) :
    outputVariableChangeHom S (MvPolynomial.X (a,j)) =
      ∑ k, MvPolynomial.X (a,k) * MvPolynomial.C (S k j) := by
  simp [outputVariableChangeHom]

omit [DecidableEq n] in
theorem outputVariableChangeHom_comp (S T : Matrix n n K) :
    (outputVariableChangeHom (m := m) S).comp (outputVariableChangeHom T) =
      outputVariableChangeHom (S*T) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [outputVariableChangeHom]
  · rintro ⟨a,j⟩
    simp only [RingHom.comp_apply,outputVariableChangeHom_X,map_sum,map_mul]
    simp only [outputVariableChangeHom,MvPolynomial.eval₂Hom_C,Matrix.mul_apply,map_sum,map_mul]
    simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    exact Finset.sum_comm

theorem outputVariableChangeHom_one :
    outputVariableChangeHom (m := m) (1 : Matrix n n K) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [outputVariableChangeHom]
  · rintro ⟨a,j⟩
    simp [outputVariableChangeHom,Matrix.one_apply]

def outputVariableChange (S T : Matrix n n K) (hST : S*T = 1) (hTS : T*S = 1) :
    MvPolynomial (m × n) K ≃+* MvPolynomial (m × n) K where
  toFun := outputVariableChangeHom S
  invFun := outputVariableChangeHom T
  left_inv p := by
    have h := RingHom.congr_fun (outputVariableChangeHom_comp (m := m) T S) p
    simpa only [RingHom.comp_apply,hTS,outputVariableChangeHom_one,RingHom.id_apply] using h
  right_inv p := by
    have h := RingHom.congr_fun (outputVariableChangeHom_comp (m := m) S T) p
    simpa only [RingHom.comp_apply,hST,outputVariableChangeHom_one,RingHom.id_apply] using h
  map_mul' := (outputVariableChangeHom S).map_mul
  map_add' := (outputVariableChangeHom S).map_add

omit [DecidableEq n] in
theorem outputVariableChangeHom_C (S : Matrix n n K) (c : K) :
    outputVariableChangeHom (m := m) S (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [outputVariableChangeHom]

omit [DecidableEq n] in
theorem outputVariableChangeHom_rows (S : Matrix n n K) :
    (Matrix.of fun a j => MvPolynomial.X (a,j) : Matrix m n (MvPolynomial (m × n) K)).map
      (outputVariableChangeHom S) =
      (Matrix.of fun a j => MvPolynomial.X (a,j)) * S.map MvPolynomial.C := by
  ext a j
  simp [outputVariableChangeHom_X,Matrix.mul_apply]

end FD56
