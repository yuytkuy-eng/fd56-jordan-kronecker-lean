/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLReconstruction

/-! The two actual auxiliary bases give a polynomial GL kernel basis at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

theorem structuredColumns_mulVec_pair
    (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (c : r × s → K[X]) :
    let C : Matrix r s K[X] := fun i j => c (i,j)
    matrixPairEquiv K[X] K[X] n m (structuredColumns M V H D T q *ᵥ c) =
      (∑ i ∈ Finset.range (q+1), M ^ i * V * C * H i,
        M ^ (q+1) * V * C * T - ∑ i ∈ Finset.range (q+1), M ^ i * V * C * D i) := by
  intro C
  apply Prod.ext
  · funext x y
    change (∑ kj, (∑ i ∈ Finset.range (q+1), (M ^ i * V) x kj.1 * H i kj.2 y) * c kj) = _
    simp only [Finset.sum_mul, Matrix.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (tensorColumns_mulVec (M ^ i * V) (H i) c) (x,y)
  · funext x y
    change (∑ kj, ((M ^ (q+1) * V) x kj.1 * T kj.2 y -
      ∑ i ∈ Finset.range (q+1), (M ^ i * V) x kj.1 * D i kj.2 y) * c kj) = _
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Matrix.sub_apply,
      Matrix.sum_apply]
    congr 1
    · exact congrFun (tensorColumns_mulVec (M ^ (q+1) * V) T c) (x,y)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (tensorColumns_mulVec (M ^ i * V) (D i) c) (x,y)

def observabilityStructuredGLMap
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i+1) * M = H i + D (i+1) * P) (hend : H q = T * P)
    (hobs : ∀ i < q+1, P * M ^ i * V = 0) :
    (r × s → K[X]) →ₗ[K[X]] LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) :=
  (Matrix.toLin' (structuredColumns M V H D T q)).codRestrict _ (by
    intro c
    have he := congrArg (fun A => A *ᵥ c)
      (structuredColumns_gl_equations M P V H D T q hzero hstep hend hobs)
    simpa only [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.zero_mulVec] using he)

theorem observabilityStructuredGLMap_bijective
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X])
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i+1) * M = H i + D (i+1) * P)
    (hend : H q = (polynomialKernelBasisMatrix _ Bt).transpose * P)
    (hobs : ∀ i < q+1, P * M ^ i * polynomialKernelBasisMatrix _ Bv = 0) :
    Function.Bijective (observabilityStructuredGLMap M P (polynomialKernelBasisMatrix _ Bv)
      H D (polynomialKernelBasisMatrix _ Bt).transpose q hzero hstep hend hobs) := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P (q+1)) Bv
  let T : Matrix s m K[X] := (polynomialKernelBasisMatrix _ Bt).transpose
  have hV := polynomialKernelBasisMatrix_injective _ Bv
  have hT : Function.Injective T.transpose.mulVec := by
    simpa only [T, Matrix.transpose_transpose] using polynomialKernelBasisMatrix_injective _ Bt
  constructor
  · intro c d h
    have hp := congrArg (fun z : LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) =>
      matrixPairEquiv K[X] K[X] n m z.val) h
    change matrixPairEquiv _ _ _ _ (structuredColumns M V H D T q *ᵥ c) =
      matrixPairEquiv _ _ _ _ (structuredColumns M V H D T q *ᵥ d) at hp
    rw [structuredColumns_mulVec_pair, structuredColumns_mulVec_pair] at hp
    have hx := congrArg Prod.fst hp
    have he := congrArg (fun Y : Matrix n n K[X] => Y * (Matrix.of fun a b => R a (Fin.last q,b))) hx
    dsimp only at he
    rw [structured_observability_terminal M P q R hR V _ H D T hstep hend,
      structured_observability_terminal M P q R hR V _ H D T hstep hend] at he
    have hc := matrix_left_mul_injective_of_mulVec _ hV
      (by simpa only [Matrix.mul_assoc] using he)
    have ht := congrArg Matrix.transpose hc
    simp only [Matrix.transpose_mul] at ht
    have hc' := matrix_left_mul_injective_of_mulVec _ hT ht
    funext k
    exact congrFun (congrFun hc' k.2) k.1
  · intro z
    let X := (matrixPairEquiv K[X] K[X] n m z.val).1
    let U := (matrixPairEquiv K[X] K[X] n m z.val).2
    obtain ⟨hPX,hres⟩ := (glEquationMatrix_kernel_iff M P z.val).mp z.property
    change P * X = 0 at hPX
    change M * X - X * M - U * P = 0 at hres
    obtain ⟨E,⟨hE,hEF⟩,_⟩ := gl_observability_terminal_beta_parameter
      M P q Bv R hR hO X U hPX (sub_eq_zero.mp hres)
    have hEt : (P * M ^ (q+1) * V).transpose * E.transpose = 0 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_zero] using congrArg Matrix.transpose hEF
    obtain ⟨Q,hQ⟩ := matrix_factor_through_kernel_basis _ Bt E.transpose hEt
    have he : E = Q.transpose * T := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose hQ
    have hp := gl_observability_structured_reconstruction M P q Bv R hR hO X U hPX
      (sub_eq_zero.mp hres) Q.transpose H D T hzero hstep hend
      (by simpa only [he, Matrix.mul_assoc] using hE)
    let c : r × s → K[X] := fun k => Q k.2 k.1
    refine ⟨c,?_⟩
    apply Subtype.ext
    apply (matrixPairEquiv K[X] K[X] n m).injective
    change matrixPairEquiv _ _ _ _ (structuredColumns M V H D T q *ᵥ c) = _
    rw [structuredColumns_mulVec_pair]
    exact Prod.ext hp.1.symm hp.2.symm

theorem observability_basis_annihilation
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (i : ℕ) (hi : i < q+1) : P * M ^ i * polynomialKernelBasisMatrix _ Bv = 0 := by
  have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P (q+1)) Bv
  funext a b
  exact congrFun (congrFun he (⟨i,hi⟩,a)) b

def observabilityGLKernelBasis
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X])
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i+1) * M = H i + D (i+1) * P)
    (hend : H q = (polynomialKernelBasisMatrix _ Bt).transpose * P) :
    Basis (r × s) K[X] (LinearMap.ker (Matrix.toLin' (glEquationMatrix M P))) :=
  (Pi.basisFun K[X] (r × s)).map (LinearEquiv.ofBijective
    (observabilityStructuredGLMap M P (polynomialKernelBasisMatrix _ Bv) H D
      (polynomialKernelBasisMatrix _ Bt).transpose q hzero hstep hend
      (observability_basis_annihilation M P q Bv))
    (observabilityStructuredGLMap_bijective M P q Bv Bt R hR hO H D hzero hstep hend
      (observability_basis_annihilation M P q Bv)))

theorem polynomialKernelBasisMatrix_observabilityGL
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec)
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X])
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i+1) * M = H i + D (i+1) * P)
    (hend : H q = (polynomialKernelBasisMatrix _ Bt).transpose * P) :
    polynomialKernelBasisMatrix (glEquationMatrix M P)
      (observabilityGLKernelBasis M P q Bv Bt R hR hO H D hzero hstep hend) =
      structuredColumns M (polynomialKernelBasisMatrix _ Bv) H D
        (polynomialKernelBasisMatrix _ Bt).transpose q := by
  funext i j
  change (structuredColumns M (polynomialKernelBasisMatrix _ Bv) H D
    (polynomialKernelBasisMatrix _ Bt).transpose q *ᵥ (Pi.basisFun K[X] (r × s) j)) i = _
  simp [Pi.basisFun_apply, Matrix.mulVec_single]

theorem exists_observability_gl_kernel_basis
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (hO : Function.Injective (observabilityMatrix M P (q+2)).mulVec) :
    Nonempty (Basis (r × s) K[X] (LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)))) := by
  let T := (polynomialKernelBasisMatrix _ Bt).transpose
  have hTF : T * (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv) = 0 := by
    have he := polynomialKernelBasisMatrix_mul _ Bt
    simpa only [T, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using
      congrArg Matrix.transpose he
  obtain ⟨H,D,hzero,hstep,hend⟩ := exists_observability_backward_rows M P q Bv R hR T hTF
  exact ⟨observabilityGLKernelBasis M P q Bv Bt R hR hO H D hzero hstep hend⟩

end FD56
