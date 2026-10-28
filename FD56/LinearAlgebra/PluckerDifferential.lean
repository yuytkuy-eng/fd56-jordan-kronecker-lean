/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MatrixDeterminantDerivation
import Mathlib.LinearAlgebra.Prod

/-! The differential of the vector of maximal row minors, including its scalar
factor, and the infinitesimal changes of column basis in its kernel. -/

noncomputable section
namespace FD56
open Matrix
variable {R m r : Type*} [CommRing R] [Fintype r] [DecidableEq r]

def pluckerMinorVector (G : Matrix m r R) : (r → m) → R :=
  fun row => (G.submatrix row id).det

def pluckerDifferential (G : Matrix m r R) :
    Matrix m r R →ₗ[R] ((r → m) → R) where
  toFun E row := Matrix.trace ((G.submatrix row id).adjugate*E.submatrix row id)
  map_add' E F := by
    ext row
    simp [Matrix.submatrix_add,Matrix.mul_add,Matrix.trace_add]
  map_smul' c E := by
    ext row
    simp [Matrix.submatrix_smul,Matrix.mul_smul,Matrix.trace_smul]

theorem pluckerDifferential_apply (G E : Matrix m r R) (row : r → m) :
    pluckerDifferential G E row=
      Matrix.trace ((G.submatrix row id).adjugate*E.submatrix row id) := rfl

theorem pluckerMinorVector_derivation {B : Type*} [CommRing B] [Algebra B R]
    (D : Derivation B R R) (G : Matrix m r R) :
    (fun row => D (pluckerMinorVector G row))=pluckerDifferential G (G.map D) := by
  ext row
  exact matrix_det_derivation D (G.submatrix row id)

theorem pluckerDifferential_mul (G : Matrix m r R) (H : Matrix r r R) :
    pluckerDifferential G (G*H)=Matrix.trace H • pluckerMinorVector G := by
  ext row
  change Matrix.trace ((G.submatrix row id).adjugate*(G*H).submatrix row id)=_
  rw [Matrix.submatrix_mul G H row id id Function.bijective_id,
    Matrix.submatrix_id_id,← Matrix.mul_assoc,Matrix.adjugate_mul,
    Matrix.smul_mul,Matrix.one_mul,Matrix.trace_smul]
  exact mul_comm _ _

def pluckerScalarDifferential (c : R) (G : Matrix m r R) :
    R × Matrix m r R →ₗ[R] ((r → m) → R) :=
  (LinearMap.fst R R (Matrix m r R)).smulRight (pluckerMinorVector G)+
    c • ((pluckerDifferential G).comp (LinearMap.snd R R (Matrix m r R)))

theorem pluckerScalarDifferential_apply (c e : R) (G E : Matrix m r R) :
    pluckerScalarDifferential c G (e,E)=e • pluckerMinorVector G+c • pluckerDifferential G E := rfl

theorem pluckerScalarMinorVector_derivation {B : Type*} [CommRing B] [Algebra B R]
    (D : Derivation B R R) (c : R) (G : Matrix m r R) :
    (fun row => D (c*pluckerMinorVector G row))=
      pluckerScalarDifferential c G (D c,G.map D) := by
  rw [pluckerScalarDifferential_apply,← pluckerMinorVector_derivation D G]
  ext row
  simp only [D.leibniz,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [add_comm,mul_comm (pluckerMinorVector G row)]

theorem pluckerScalarDifferential_endomorphism_zero
    (c : R) (G : Matrix m r R) (H : Matrix r r R) :
    pluckerScalarDifferential c G (-c*Matrix.trace H,G*H)=0 := by
  rw [pluckerScalarDifferential_apply,pluckerDifferential_mul,
    neg_mul,neg_smul,MulAction.mul_smul,neg_add_cancel]

omit [DecidableEq r] in
theorem plucker_endomorphism_pair_injective (c : R) (G : Matrix m r R)
    (hG : Function.Injective G.mulVec) :
    Function.Injective (fun H : Matrix r r R => (-c*Matrix.trace H,G*H)) := by
  intro H J h
  have hh : G*H=G*J := congrArg Prod.snd h
  funext i j
  have hc : (fun k => H k j)=(fun k => J k j) := by
    apply hG
    funext x
    exact congrFun (congrFun hh x) j
  exact congrFun hc i

end FD56
