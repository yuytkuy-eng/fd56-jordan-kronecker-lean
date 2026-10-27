/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil
import Mathlib.Data.Matrix.Kronecker

/-! State and output basis changes, including the exact Kirillov determinant weight. -/

noncomputable section
namespace FD56
open Matrix
open scoped Kronecker

variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def glRectangularBasisLinear (S T : Matrix n n R) (W : Matrix m m R) :
    (SLInput n m → R) →ₗ[R] (SLInput n m → R) where
  toFun v := (matrixPairEquiv R R n m).symm
    (S*(matrixPairEquiv R R n m v).1*T,S*(matrixPairEquiv R R n m v).2*W)
  map_add' v w := by
    simp only [map_add,Prod.fst_add,Prod.snd_add,Matrix.mul_add,Matrix.add_mul,← Prod.mk_add_mk]
  map_smul' c v := by
    simp only [map_smul,Prod.smul_fst,Prod.smul_snd,Matrix.mul_smul,Matrix.smul_mul,
      ← Prod.smul_mk,RingHom.id_apply]

def glRectangularBasisChange (S T : Matrix n n R) (W : Matrix m m R) :
    Matrix (SLInput n m) (SLInput n m) R := LinearMap.toMatrix' (glRectangularBasisLinear S T W)

theorem glRectangularBasisChange_mulVec (S T : Matrix n n R) (W : Matrix m m R)
    (v : SLInput n m → R) :
    matrixPairEquiv R R n m (glRectangularBasisChange S T W*ᵥv)=
      (S*(matrixPairEquiv R R n m v).1*T,S*(matrixPairEquiv R R n m v).2*W) := by
  rw [← Matrix.toLin'_apply,glRectangularBasisChange,Matrix.toLin'_toMatrix']
  exact (matrixPairEquiv R R n m).apply_symm_apply _

theorem glRectangularBasisChange_inverse (S T : Matrix n n R) (W Z : Matrix m m R)
    (hST : S*T=1) (hZW : Z*W=1) :
    glRectangularBasisChange S T W*glRectangularBasisChange T S Z=1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_one]
  apply LinearMap.ext
  intro v
  apply (matrixPairEquiv R R n m).injective
  change matrixPairEquiv R R n m
    (glRectangularBasisChange S T W*ᵥ(glRectangularBasisChange T S Z*ᵥv))=_
  rw [glRectangularBasisChange_mulVec,glRectangularBasisChange_mulVec]
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc S T,hST,Matrix.one_mul,
    Matrix.mul_one,← Matrix.mul_assoc Z W,hZW]
  rfl

theorem glKirillovMatrix_rectangular_bracket (M : Matrix n n R) (P : Matrix m n R)
    (v w : SLInput n m → R) :
    w ⬝ᵥ (glKirillovMatrix M P*ᵥv)=
      Matrix.trace (M*((matrixPairEquiv R R n m v).1*(matrixPairEquiv R R n m w).1-
        (matrixPairEquiv R R n m w).1*(matrixPairEquiv R R n m v).1))+
      Matrix.trace (P*((matrixPairEquiv R R n m v).1*(matrixPairEquiv R R n m w).2-
        (matrixPairEquiv R R n m w).1*(matrixPairEquiv R R n m v).2)) := by
  rw [glKirillovMatrix_pairing_equations]
  let X := (matrixPairEquiv R R n m v).1
  let U := (matrixPairEquiv R R n m v).2
  let Y := (matrixPairEquiv R R n m w).1
  let V := (matrixPairEquiv R R n m w).2
  change Matrix.trace ((M*X-X*M-U*P)*Y)+Matrix.trace ((P*X)*V)=
    Matrix.trace (M*(X*Y-Y*X))+Matrix.trace (P*(X*V-Y*U))
  have h1 : Matrix.trace (M*(Y*X))=Matrix.trace ((X*M)*Y) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle M Y X]
  have h2 : Matrix.trace (P*(Y*U))=Matrix.trace ((U*P)*Y) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle P Y U]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub]
  rw [← h1,← h2]
  simp only [Matrix.mul_assoc]
  ring

omit [DecidableEq m] in
theorem rectangularGL_pairing_basis_change (S T M X Y : Matrix n n R)
    (W : Matrix m m R) (P : Matrix m n R) (U V : Matrix n m R) (hTS : T*S=1) :
    Matrix.trace (M*((S*X*T)*(S*Y*T)-(S*Y*T)*(S*X*T)))+
      Matrix.trace (P*((S*X*T)*(S*V*W)-(S*Y*T)*(S*U*W)))=
    Matrix.trace ((T*M*S)*(X*Y-Y*X))+Matrix.trace ((W*P*S)*(X*V-Y*U)) := by
  have hmul (A B C : Matrix n n R) : (S*A*T)*(S*B*C)=S*(A*B)*C := by
    calc
      _ = S*A*(T*S)*B*C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTS]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  have hmulrow (A : Matrix n n R) (B : Matrix n m R) :
      (S*A*T)*(S*B*W)=S*(A*B)*W := by
    calc
      _ = S*A*(T*S)*B*W := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTS]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  rw [hmul X Y T,hmul Y X T,hmulrow X V,hmulrow Y U]
  rw [← Matrix.sub_mul,← Matrix.mul_sub,← Matrix.sub_mul,← Matrix.mul_sub]
  have hstate : Matrix.trace (M*(S*(X*Y-Y*X)*T))=Matrix.trace ((T*M*S)*(X*Y-Y*X)) := by
    rw [← Matrix.mul_assoc M,← Matrix.mul_assoc,Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  have hrow : Matrix.trace (P*(S*(X*V-Y*U)*W))=Matrix.trace ((W*P*S)*(X*V-Y*U)) := by
    rw [← Matrix.mul_assoc P,← Matrix.mul_assoc,Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [hstate,hrow]

theorem glRectangularBasisChange_congruence (S T M : Matrix n n R) (W : Matrix m m R)
    (P : Matrix m n R) (hTS : T*S=1) :
    (glRectangularBasisChange S T W).transpose*glKirillovMatrix M P*glRectangularBasisChange S T W=
      glKirillovMatrix (T*M*S) (W*P*S) := by
  have hp (v w : SLInput n m → R) :
      w ⬝ᵥ (((glRectangularBasisChange S T W).transpose*glKirillovMatrix M P*
        glRectangularBasisChange S T W)*ᵥv)=w ⬝ᵥ (glKirillovMatrix (T*M*S) (W*P*S)*ᵥv) := by
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    rw [glKirillovMatrix_rectangular_bracket,glKirillovMatrix_rectangular_bracket,
      glRectangularBasisChange_mulVec,glRectangularBasisChange_mulVec]
    exact rectangularGL_pairing_basis_change S T M _ _ W P _ _ hTS
  ext i j
  simpa only [Matrix.mulVec_single_one,single_dotProduct,one_mul] using hp (Pi.single j 1) (Pi.single i 1)

theorem glRectangularBasisChange_blocks (S T : Matrix n n R) (W : Matrix m m R) :
    glRectangularBasisChange S T W=
      Matrix.fromBlocks (S ⊗ₖ T.transpose) 0 0 (S ⊗ₖ W.transpose) := by
  ext x y
  rcases x with ⟨i,j⟩|⟨i,j⟩ <;> rcases y with ⟨a,b⟩|⟨a,b⟩
  all_goals simp [glRectangularBasisChange,glRectangularBasisLinear,LinearMap.toMatrix'_apply,
    matrixPairEquiv,Matrix.mul_apply,Pi.single_apply,Matrix.kronecker_apply,ite_and]

theorem glRectangularBasisChange_det (S T : Matrix n n R) (W : Matrix m m R) (hST : S*T=1) :
    (glRectangularBasisChange S T W).det=S.det^Fintype.card m*W.det^Fintype.card n := by
  have hdet : S.det*T.det=1 := by rw [← Matrix.det_mul,hST,Matrix.det_one]
  rw [glRectangularBasisChange_blocks,Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_kronecker,Matrix.det_kronecker,Matrix.det_transpose,Matrix.det_transpose,
    ← mul_pow,hdet,one_pow,one_mul]

theorem glKirillovMatrix_det_basis_change (S T M : Matrix n n R) (W : Matrix m m R)
    (P : Matrix m n R) (hST : S*T=1) (hTS : T*S=1) :
    (glKirillovMatrix (T*M*S) (W*P*S)).det=
      (S.det^Fintype.card m*W.det^Fintype.card n)^2*(glKirillovMatrix M P).det := by
  rw [← glRectangularBasisChange_congruence S T M W P hTS,
    Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,glRectangularBasisChange_det S T W hST]
  ring

end FD56
