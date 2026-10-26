/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.OutputVariableChange
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-! Invertible changes of independent matrix-row variables. -/

noncomputable section
namespace FD56
open Matrix MvPolynomial
open scoped BigOperators
variable {K n m : Type*} [CommRing K] [Fintype n] [DecidableEq n]

def inputVariableChangeHom (S : Matrix n n K) :
    MvPolynomial (n × m) K →+* MvPolynomial (n × m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun ij => ∑ k, MvPolynomial.C (S ij.1 k) * MvPolynomial.X (k,ij.2))

omit [DecidableEq n] in
theorem inputVariableChangeHom_X (S : Matrix n n K) (i : n) (j : m) :
    inputVariableChangeHom S (MvPolynomial.X (i,j)) =
      ∑ k, MvPolynomial.C (S i k) * MvPolynomial.X (k,j) := by
  simp [inputVariableChangeHom]

omit [DecidableEq n] in
theorem inputVariableChangeHom_C (S : Matrix n n K) (c : K) :
    inputVariableChangeHom (m := m) S (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [inputVariableChangeHom]

omit [DecidableEq n] in
theorem inputVariableChangeHom_comp (S T : Matrix n n K) :
    (inputVariableChangeHom (m := m) S).comp (inputVariableChangeHom T) =
      inputVariableChangeHom (T*S) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [inputVariableChangeHom]
  · rintro ⟨i,j⟩
    simp only [RingHom.comp_apply,inputVariableChangeHom_X,map_sum,map_mul,
      inputVariableChangeHom_C,Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    exact Finset.sum_comm

theorem inputVariableChangeHom_one :
    inputVariableChangeHom (m := m) (1 : Matrix n n K) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [inputVariableChangeHom]
  · rintro ⟨i,j⟩
    simp [inputVariableChangeHom,Matrix.one_apply]

def inputVariableChange (S T : Matrix n n K) (hST : S*T=1) (hTS : T*S=1) :
    MvPolynomial (n × m) K ≃+* MvPolynomial (n × m) K where
  toFun := inputVariableChangeHom S
  invFun := inputVariableChangeHom T
  left_inv p := by
    have h := RingHom.congr_fun (inputVariableChangeHom_comp (m := m) T S) p
    simpa only [RingHom.comp_apply,hST,inputVariableChangeHom_one,RingHom.id_apply] using h
  right_inv p := by
    have h := RingHom.congr_fun (inputVariableChangeHom_comp (m := m) S T) p
    simpa only [RingHom.comp_apply,hTS,inputVariableChangeHom_one,RingHom.id_apply] using h
  map_mul' := (inputVariableChangeHom S).map_mul
  map_add' := (inputVariableChangeHom S).map_add

theorem inputVariableChangeHom_injective (S T : Matrix n n K) (hST : S*T=1) (hTS : T*S=1) :
    Function.Injective (inputVariableChangeHom (m := m) S) :=
  (inputVariableChange S T hST hTS).injective

omit [DecidableEq n] in
theorem inputVariableChangeHom_matrix (S : Matrix n n K) :
    (Matrix.mvPolynomialX n m K).map (inputVariableChangeHom S) =
      S.map MvPolynomial.C * Matrix.mvPolynomialX n m K := by
  ext i j
  simp [Matrix.mvPolynomialX,inputVariableChangeHom_X,Matrix.mul_apply]

omit [DecidableEq n] in
theorem inputVariableChangeHom_matrix_map_neg {E : Type*} [CommRing E]
    (phi : MvPolynomial (n × m) K →+* E) (S : Matrix n n K) :
    (fun i j => phi (inputVariableChangeHom (-S) (MvPolynomial.X (i,j)))) =
      -(S.map (phi.comp MvPolynomial.C)) * (Matrix.mvPolynomialX n m K).map phi := by
  ext i j
  simp [inputVariableChangeHom_X,Matrix.mul_apply,Matrix.mvPolynomialX]

end FD56
