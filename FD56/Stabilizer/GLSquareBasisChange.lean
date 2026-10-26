/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil

/-! Constant changes of state and row coordinates in the actual square GL
Kirillov form. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

def glSquareBasisLinear (S T W : Matrix n n R) :
    (SLInput n n → R) →ₗ[R] (SLInput n n → R) where
  toFun v := (matrixPairEquiv R R n n).symm
    (S*(matrixPairEquiv R R n n v).1*T,S*(matrixPairEquiv R R n n v).2*W)
  map_add' v w := by
    simp only [map_add,Prod.fst_add,Prod.snd_add,Matrix.mul_add,Matrix.add_mul,
      ← Prod.mk_add_mk]
  map_smul' c v := by
    simp only [map_smul,Prod.smul_fst,Prod.smul_snd,Matrix.mul_smul,Matrix.smul_mul,
      ← Prod.smul_mk,RingHom.id_apply]

def glSquareBasisChange (S T W : Matrix n n R) : Matrix (SLInput n n) (SLInput n n) R :=
  LinearMap.toMatrix' (glSquareBasisLinear S T W)

theorem glSquareBasisChange_mulVec (S T W : Matrix n n R) (v : SLInput n n → R) :
    matrixPairEquiv R R n n (glSquareBasisChange S T W *ᵥ v) =
      (S*(matrixPairEquiv R R n n v).1*T,S*(matrixPairEquiv R R n n v).2*W) := by
  rw [← Matrix.toLin'_apply,glSquareBasisChange,Matrix.toLin'_toMatrix']
  exact (matrixPairEquiv R R n n).apply_symm_apply _

theorem glSquareBasisChange_inverse (S T W Z : Matrix n n R)
    (hST : S*T=1) (hZW : Z*W=1) :
    glSquareBasisChange S T W * glSquareBasisChange T S Z = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_one]
  apply LinearMap.ext
  intro v
  apply (matrixPairEquiv R R n n).injective
  change matrixPairEquiv R R n n
    (glSquareBasisChange S T W *ᵥ (glSquareBasisChange T S Z *ᵥ v)) = _
  rw [glSquareBasisChange_mulVec,glSquareBasisChange_mulVec]
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc S T,hST,Matrix.one_mul,
    Matrix.mul_one,← Matrix.mul_assoc Z W,hZW]
  rfl

theorem glKirillovMatrix_pairing_bracket (M P : Matrix n n R) (v w : SLInput n n → R) :
    w ⬝ᵥ (glKirillovMatrix M P *ᵥ v) =
      Matrix.trace (M*((matrixPairEquiv R R n n v).1*(matrixPairEquiv R R n n w).1-
        (matrixPairEquiv R R n n w).1*(matrixPairEquiv R R n n v).1)) +
      Matrix.trace (P*((matrixPairEquiv R R n n v).1*(matrixPairEquiv R R n n w).2-
        (matrixPairEquiv R R n n w).1*(matrixPairEquiv R R n n v).2)) := by
  rw [glKirillovMatrix_pairing_equations]
  let X := (matrixPairEquiv R R n n v).1
  let U := (matrixPairEquiv R R n n v).2
  let Y := (matrixPairEquiv R R n n w).1
  let V := (matrixPairEquiv R R n n w).2
  change Matrix.trace ((M*X-X*M-U*P)*Y) + Matrix.trace ((P*X)*V) =
    Matrix.trace (M*(X*Y-Y*X)) + Matrix.trace (P*(X*V-Y*U))
  have h1 : Matrix.trace (M*(Y*X)) = Matrix.trace ((X*M)*Y) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle M Y X]
  have h2 : Matrix.trace (P*(Y*U)) = Matrix.trace ((U*P)*Y) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle P Y U]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub]
  rw [← h1,← h2]
  simp only [Matrix.mul_assoc]
  ring

theorem squareGL_pairing_basis_change (S T W M P X U Y V : Matrix n n R)
    (hTS : T*S=1) :
    Matrix.trace (M*((S*X*T)*(S*Y*T)-(S*Y*T)*(S*X*T))) +
      Matrix.trace (P*((S*X*T)*(S*V*W)-(S*Y*T)*(S*U*W))) =
    Matrix.trace ((T*M*S)*(X*Y-Y*X)) + Matrix.trace ((W*P*S)*(X*V-Y*U)) := by
  have hmul (A B C : Matrix n n R) : (S*A*T)*(S*B*C)=S*(A*B)*C := by
    calc
      _ = S*A*(T*S)*B*C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTS]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  rw [hmul X Y T,hmul Y X T,hmul X V W,hmul Y U W]
  rw [← Matrix.sub_mul,← Matrix.mul_sub,← Matrix.sub_mul,← Matrix.mul_sub]
  have htrace (A B C D : Matrix n n R) :
      Matrix.trace (A*(B*C*D)) = Matrix.trace ((D*A*B)*C) := by
    rw [← Matrix.mul_assoc A,← Matrix.mul_assoc,Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [htrace,htrace]

theorem glSquareBasisChange_congruence (S T W M P : Matrix n n R) (hTS : T*S=1) :
    (glSquareBasisChange S T W).transpose * glKirillovMatrix M P * glSquareBasisChange S T W =
      glKirillovMatrix (T*M*S) (W*P*S) := by
  have hpair (v w : SLInput n n → R) :
      w ⬝ᵥ (((glSquareBasisChange S T W).transpose * glKirillovMatrix M P *
        glSquareBasisChange S T W) *ᵥ v) =
      w ⬝ᵥ (glKirillovMatrix (T*M*S) (W*P*S) *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    rw [glKirillovMatrix_pairing_bracket,glKirillovMatrix_pairing_bracket]
    rw [glSquareBasisChange_mulVec,glSquareBasisChange_mulVec]
    exact squareGL_pairing_basis_change S T W M P _ _ _ _ hTS
  ext i j
  simpa only [Matrix.mulVec_single_one,single_dotProduct,one_mul] using
    hpair (Pi.single j 1) (Pi.single i 1)

theorem glSquareBasisChange_map {L : Type*} [CommRing L] (f : R →+* L)
    (S T W : Matrix n n R) :
    (glSquareBasisChange S T W).map f = glSquareBasisChange (S.map f) (T.map f) (W.map f) := by
  ext i j
  cases i <;> cases j <;>
    simp [glSquareBasisChange,LinearMap.toMatrix'_apply,glSquareBasisLinear,
      matrixPairEquiv,Matrix.mul_apply,map_sum,map_mul,Pi.single_apply,apply_ite]

end FD56
