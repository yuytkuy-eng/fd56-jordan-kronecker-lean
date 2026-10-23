/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoGLNormalForm

/-! A polynomial basis of the actual GL equations in the second observability range. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r s : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s]

def depthTwoGLColumns (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ : Matrix s m K[X]) :
    Matrix (SLInput n m) (r × s) K[X] :=
  Sum.elim
    (fun xy kj => V xy.1 kj.1 * (T*P*M-D₁*P) kj.2 xy.2 +
      (M*V) xy.1 kj.1 * (T*P) kj.2 xy.2)
    (fun xy kj => (M*M*V) xy.1 kj.1 * T kj.2 xy.2 -
      (M*V) xy.1 kj.1 * D₁ kj.2 xy.2 - V xy.1 kj.1 * D₀ kj.2 xy.2)

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] in
theorem depthTwoGLColumns_mulVec (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ : Matrix s m K[X]) (c : r × s → K[X]) :
    let C : Matrix r s K[X] := fun i j => c (i,j)
    matrixPairEquiv K[X] K[X] n m (depthTwoGLColumns M P V T D₀ D₁ *ᵥ c) =
      (V*C*(T*P*M-D₁*P)+M*V*C*T*P,
        M*M*V*C*T-M*V*C*D₁-V*C*D₀) := by
  intro C
  apply Prod.ext
  · funext x y
    change (∑ kj, (V x kj.1 * (T*P*M-D₁*P) kj.2 y +
      (M*V) x kj.1 * (T*P) kj.2 y) * c kj) = _
    simp only [add_mul,Finset.sum_add_distrib,Matrix.add_apply]
    have h₀ := congrFun (tensorColumns_mulVec V (T*P*M-D₁*P) c) (x,y)
    have h₁ := congrFun (tensorColumns_mulVec (M*V) (T*P) c) (x,y)
    exact congrArg₂ (fun a b : K[X] => a+b) h₀
      (by simpa only [Matrix.mul_assoc,C] using h₁)
  · funext x y
    change (∑ kj, ((M*M*V) x kj.1 * T kj.2 y -
      (M*V) x kj.1 * D₁ kj.2 y - V x kj.1 * D₀ kj.2 y) * c kj) = _
    simp only [sub_mul,Finset.sum_sub_distrib,Matrix.sub_apply]
    exact congrArg₂ (fun a b : K[X] => a-b)
      (congrArg₂ (fun a b : K[X] => a-b)
        (congrFun (tensorColumns_mulVec (M*M*V) T c) (x,y))
        (congrFun (tensorColumns_mulVec (M*V) D₁ c) (x,y)))
      (congrFun (tensorColumns_mulVec V D₀ c) (x,y))

omit [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] in
theorem depthTwo_gl_pair_equations (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (E D₀ D₁ : Matrix r m K[X])
    (hPV : P*V=0) (hPMV : P*M*V=0)
    (hrel : E*P*M*M=D₀*P+D₁*(P*M)) :
    P*(V*(E*P*M-D₁*P)+M*V*E*P)=0 ∧
      M*(V*(E*P*M-D₁*P)+M*V*E*P) -
        (V*(E*P*M-D₁*P)+M*V*E*P)*M =
          (M*M*V*E-M*V*D₁-V*D₀)*P := by
  constructor
  · simp only [Matrix.mul_add,← Matrix.mul_assoc,hPV,hPMV,Matrix.zero_mul,add_zero]
  · have hh := congrArg (fun A : Matrix r n K[X] => V*A) hrel
    simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_assoc] at hh ⊢
    rw [hh]
    abel

def depthTwoGLMap (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ : Matrix s m K[X])
    (hPV : P*V=0) (hPMV : P*M*V=0)
    (hrel : T*P*M*M=D₀*P+D₁*(P*M)) :
    (r × s → K[X]) →ₗ[K[X]] LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) :=
  (Matrix.toLin' (depthTwoGLColumns M P V T D₀ D₁)).codRestrict _ (by
    intro c
    apply (glEquationMatrix_kernel_iff M P _).mpr
    rw [Matrix.toLin'_apply,depthTwoGLColumns_mulVec]
    let C : Matrix r s K[X] := fun i j => c (i,j)
    have hr : (C*T)*P*M*M=(C*D₀)*P+(C*D₁)*(P*M) := by
      have hh := congrArg (fun A : Matrix s n K[X] => C*A) hrel
      simpa only [Matrix.mul_add,Matrix.mul_assoc] using hh
    have hh := depthTwo_gl_pair_equations M P V (C*T) (C*D₀) (C*D₁) hPV hPMV hr
    constructor
    · simpa only [C,Matrix.mul_sub,Matrix.mul_assoc] using hh.1
    · apply sub_eq_zero.mpr
      simpa only [C,Matrix.mul_sub,Matrix.mul_assoc] using hh.2)

theorem depthTwoGLMap_bijective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).transpose)))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (D₀ D₁ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*M*M=D₀*P+D₁*(P*M))
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).mulVec) :
    Function.Bijective (depthTwoGLMap M P (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv)
      (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁
      ((depthTwo_stack_mul_zero_iff _ _ _).mp (polynomialKernelBasisMatrix_mul _ Bv)).1
      ((depthTwo_stack_mul_zero_iff _ _ _).mp (polynomialKernelBasisMatrix_mul _ Bv)).2 hrel) := by
  let V := polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv
  let T := (polynomialKernelBasisMatrix (P*M*M*V).transpose Bt).transpose
  have hV := polynomialKernelBasisMatrix_injective _ Bv
  have hT : Function.Injective T.transpose.mulVec := by
    simpa [T] using polynomialKernelBasisMatrix_injective _ Bt
  constructor
  · intro c d h
    have hp := congrArg (fun z : LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) =>
      matrixPairEquiv K[X] K[X] n m z.val) h
    change matrixPairEquiv _ _ _ _ (depthTwoGLColumns M P V T D₀ D₁ *ᵥ c) =
      matrixPairEquiv _ _ _ _ (depthTwoGLColumns M P V T D₀ D₁ *ᵥ d) at hp
    rw [depthTwoGLColumns_mulVec,depthTwoGLColumns_mulVec] at hp
    let C : Matrix r s K[X] := fun i j => c (i,j)
    let C' : Matrix r s K[X] := fun i j => d (i,j)
    have he : C*T=C'*T := by
      apply depthTwo_gl_parameter_unique M P V hV R hR (C*T) (C'*T) (C*D₁) (C'*D₁)
      simpa only [C,C',Matrix.mul_sub,Matrix.mul_assoc] using congrArg Prod.fst hp
    have ht := congrArg Matrix.transpose he
    simp only [Matrix.transpose_mul] at ht
    have hc := matrix_left_mul_injective_of_mulVec _ hT ht
    funext k
    exact congrFun (congrFun hc k.2) k.1
  · intro z
    let X := (matrixPairEquiv K[X] K[X] n m z.val).1
    let U := (matrixPairEquiv K[X] K[X] n m z.val).2
    obtain ⟨hPX,hres⟩ := (glEquationMatrix_kernel_iff M P z.val).mp z.property
    change P*X=0 at hPX
    change M*X-X*M-U*P=0 at hres
    obtain ⟨E,F₀,F₁,hEF,hr,hX,hU⟩ := depthTwo_gl_normal_form M P Bv R hR hF X U
      hPX (sub_eq_zero.mp hres)
    change E*(P*M*M*V)=0 at hEF
    have hEt : (P*M*M*V).transpose*E.transpose=0 := by
      simpa only [Matrix.transpose_mul,Matrix.transpose_zero] using congrArg Matrix.transpose hEF
    obtain ⟨Q,hQ⟩ := matrix_factor_through_kernel_basis _ Bt E.transpose hEt
    have hE : E=Q.transpose*T := by
      simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using congrArg Matrix.transpose hQ
    have hD : Matrix.fromCols F₀ F₁ = Matrix.fromCols (Q.transpose*D₀) (Q.transpose*D₁) := by
      apply row_factor_unique_of_right_inverse _ R hR
      change Matrix.fromCols F₀ F₁ * Matrix.fromRows P (P*M) =
        Matrix.fromCols (Q.transpose*D₀) (Q.transpose*D₁) * Matrix.fromRows P (P*M)
      rw [Matrix.fromCols_mul_fromRows,Matrix.fromCols_mul_fromRows,← hr,hE]
      have hh := congrArg (fun A : Matrix s n K[X] => Q.transpose*A) hrel
      simpa only [T,Matrix.mul_add,Matrix.mul_assoc] using hh
    have hD₀ : F₀=Q.transpose*D₀ := by
      funext i j; exact congrFun (congrFun hD i) (Sum.inl j)
    have hD₁ : F₁=Q.transpose*D₁ := by
      funext i j; exact congrFun (congrFun hD i) (Sum.inr j)
    let c : r × s → K[X] := fun k => Q k.2 k.1
    refine ⟨c,?_⟩
    apply Subtype.ext
    apply (matrixPairEquiv K[X] K[X] n m).injective
    change matrixPairEquiv _ _ _ _ (depthTwoGLColumns M P V T D₀ D₁ *ᵥ c) = _
    rw [depthTwoGLColumns_mulVec]
    apply Prod.ext
    · change _=X
      rw [hX,hE,hD₁]
      simp only [c,V,Matrix.transpose_apply,Matrix.mul_sub,Matrix.mul_assoc]
      rfl
    · change _=U
      rw [hU,hE,hD₀,hD₁]
      simp only [c,V,Matrix.transpose_apply,Matrix.mul_assoc]
      rfl

def depthTwoGLKernelBasis (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).transpose)))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (D₀ D₁ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*M*M=D₀*P+D₁*(P*M))
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).mulVec) :
    Basis (r × s) K[X] (LinearMap.ker (Matrix.toLin' (glEquationMatrix M P))) :=
  (Pi.basisFun K[X] (r × s)).map (LinearEquiv.ofBijective
    (depthTwoGLMap M P (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv)
      (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁
      ((depthTwo_stack_mul_zero_iff _ _ _).mp (polynomialKernelBasisMatrix_mul _ Bv)).1
      ((depthTwo_stack_mul_zero_iff _ _ _).mp (polynomialKernelBasisMatrix_mul _ Bv)).2 hrel)
    (depthTwoGLMap_bijective M P Bv Bt R hR D₀ D₁ hrel hF))

theorem polynomialKernelBasisMatrix_depthTwoGL (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).transpose)))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (D₀ D₁ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*M*M=D₀*P+D₁*(P*M))
    (hF : Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv).mulVec) :
    polynomialKernelBasisMatrix (glEquationMatrix M P)
      (depthTwoGLKernelBasis M P Bv Bt R hR D₀ D₁ hrel hF) =
      depthTwoGLColumns M P (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv)
        (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ := by
  funext i j
  change (depthTwoGLColumns M P (polynomialKernelBasisMatrix (depthTwoStack P (P*M)) Bv)
    (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ *ᵥ (Pi.basisFun K[X] (r × s) j)) i = _
  simp [Pi.basisFun_apply,Matrix.mulVec_single]

omit [Fintype s] [DecidableEq r] [DecidableEq s] in
theorem exists_depthTwo_beta_coefficients (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M)*R=1)
    (T : Matrix s m K[X])
    (hT : T*(P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B)=0) :
    ∃ D₀ D₁ : Matrix s m K[X], T*P*M*M=D₀*P+D₁*(P*M) := by
  have hV : (T*P*M*M)*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B=0 := by
    simpa only [Matrix.mul_assoc] using hT
  have he := row_factor_through_of_kernel_basis _ B R hR (T*P*M*M) hV
  refine ⟨fun i j => (T*P*M*M*R) i (Sum.inl j),
    fun i j => (T*P*M*M*R) i (Sum.inr j),?_⟩
  conv_lhs => rw [he]
  funext i j
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,depthTwoStack,Sum.elim_inl,
    Sum.elim_inr,Matrix.add_apply]

end FD56
