/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil
import FD56.Stabilizer.GenericRows
import FD56.Hilbert.RegularJordanBlock

/-! The scalar square GL pencil has exactly one regular block of dimension two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def scalarGLRegularChange (b : K) : Matrix (SLInput (Fin 1) (Fin 1)) (Fin 1 ⊕ Fin 1) K :=
  fun i j => match i,j with
    | .inl _,.inl _ => 1
    | .inr _,.inr _ => -b⁻¹
    | _,_ => 0

def scalarGLRegularInverse (b : K) : Matrix (Fin 1 ⊕ Fin 1) (SLInput (Fin 1) (Fin 1)) K :=
  fun i j => match i,j with
    | .inl _,.inl _ => 1
    | .inr _,.inr _ => -b
    | _,_ => 0

theorem scalarGLRegular_inverse (b : K) (hb : b≠0) :
    scalarGLRegularChange b * scalarGLRegularInverse b=1 ∧
      scalarGLRegularInverse b * scalarGLRegularChange b=1 := by
  constructor
  · ext i j
    rcases i with ⟨i,k⟩ | ⟨i,k⟩ <;> rcases j with ⟨j,l⟩ | ⟨j,l⟩ <;>
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [scalarGLRegularChange,scalarGLRegularInverse,Matrix.mul_apply,
        Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.one_apply,hb]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [scalarGLRegularChange,scalarGLRegularInverse,Matrix.mul_apply,
        Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.one_apply,hb]

theorem scalarGLRegular_congruence (M : Matrix (Fin 1) (Fin 1) K[X])
    (a b : K) (hb : b≠0) :
    ((scalarGLRegularChange b).map C).transpose *
        glKirillovMatrix M (fun _ _ => C a+X*C b) * (scalarGLRegularChange b).map C =
      skewJordanBlockPencil (-a/b) 1 := by
  funext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [scalarGLRegularChange,glKirillovMatrix,glTraceDualIndexEquiv,
      glEquationMatrix,LinearMap.toMatrix'_apply,glEquationLinearMap,matrixPairEquiv,
      stabilizerResidual,Matrix.mul_apply,Fintype.sum_sum_type,Fintype.sum_prod_type,
      Fin.sum_univ_succ,Pi.single_apply,skewJordanBlockPencil,jordanUpperPencil]
  all_goals have hb' : (C b : K[X]) * C b⁻¹=1 := by rw [← map_mul,mul_inv_cancel₀ hb,map_one]
  all_goals simp only [map_neg,div_eq_mul_inv,map_mul]
  all_goals first | linear_combination X * hb' | linear_combination -X * hb'

theorem squareGL_scalar_jordan_decomposition (M : Matrix (Fin 1) (Fin 1) K[X])
    (a b : K) (hb : b≠0) :
    ∃ G : Matrix (SLInput (Fin 1) (Fin 1)) (Fin 1 ⊕ Fin 1) K,
    ∃ H : Matrix (Fin 1 ⊕ Fin 1) (SLInput (Fin 1) (Fin 1)) K,
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose * glKirillovMatrix M (fun _ _ => C a+X*C b) * G.map C =
        skewJordanBlockPencil (-a/b) 1 :=
  ⟨scalarGLRegularChange b,scalarGLRegularInverse b,(scalarGLRegular_inverse b hb).1,
    (scalarGLRegular_inverse b hb).2,scalarGLRegular_congruence M a b hb⟩

theorem generic_square_gl_scalar_jordan_decomposition :
    ∃ lam : AffineCoefficientField K (MatrixParameters (Fin 1) (Fin 1)),
    ∃ G : Matrix (SLInput (Fin 1) (Fin 1)) (Fin 1 ⊕ Fin 1)
      (AffineCoefficientField K (MatrixParameters (Fin 1) (Fin 1))),
    ∃ H : Matrix (Fin 1 ⊕ Fin 1) (SLInput (Fin 1) (Fin 1))
      (AffineCoefficientField K (MatrixParameters (Fin 1) (Fin 1))),
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose *
          glKirillovMatrix (genericAffineSquare K (Fin 1) (Fin 1))
            (genericAffineRows K (Fin 1) (Fin 1)) * G.map C = skewJordanBlockPencil lam 1 := by
  let F := AffineCoefficientField K (MatrixParameters (Fin 1) (Fin 1))
  let psi : MvPolynomial (MatrixParameters (Fin 1) (Fin 1) ⊕ MatrixParameters (Fin 1) (Fin 1)) K →+* F :=
    algebraMap _ F
  let a := psi (MvPolynomial.X (.inl (.inr (0,0))))
  let b := psi (MvPolynomial.X (.inr (.inr (0,0))))
  have hb : b≠0 := (map_ne_zero_iff psi (IsFractionRing.injective _ _)).mpr (MvPolynomial.X_ne_zero _)
  obtain ⟨G,H,hGH,hHG,hcong⟩ :=
    squareGL_scalar_jordan_decomposition (genericAffineSquare K (Fin 1) (Fin 1)) a b hb
  refine ⟨-a/b,G,H,hGH,hHG,?_⟩
  have hrow : genericAffineRows K (Fin 1) (Fin 1) = (fun _ _ => C a+X*C b) := by
    funext i j
    fin_cases i
    fin_cases j
    simp [genericAffineRows,universalRows,affineParameterMap,a,b,psi,F]
  rwa [hrow]

end FD56
