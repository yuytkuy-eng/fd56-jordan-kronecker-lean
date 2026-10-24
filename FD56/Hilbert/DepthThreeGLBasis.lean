/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeGLReconstruction
import FD56.Hilbert.MiddleGL
import FD56.Hilbert.GenericDepthThreeRightInverse

/-! A polynomial basis of the third-depth GL equations from the two auxiliary bases. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

def depthThreeGLColumns (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ D₂ : Matrix s m K[X]) :
    Matrix (SLInput n m) (r × s) K[X] :=
  Sum.elim
    (fun xy kj => V xy.1 kj.1*(T*P*(M^2 : Matrix n n K[X])-D₂*(P*M)-D₁*P) kj.2 xy.2+
      (M*V) xy.1 kj.1*(T*P*M-D₂*P) kj.2 xy.2+
      ((M^2 : Matrix n n K[X])*V) xy.1 kj.1*(T*P) kj.2 xy.2)
    (fun xy kj => ((M^3 : Matrix n n K[X])*V) xy.1 kj.1*T kj.2 xy.2-
      ((M^2 : Matrix n n K[X])*V) xy.1 kj.1*D₂ kj.2 xy.2-
      (M*V) xy.1 kj.1*D₁ kj.2 xy.2-V xy.1 kj.1*D₀ kj.2 xy.2)

omit [DecidableEq m] [DecidableEq r] [DecidableEq s] in
theorem depthThreeGLColumns_mulVec (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ D₂ : Matrix s m K[X]) (c : r × s → K[X]) :
    let C : Matrix r s K[X] := fun i j => c (i,j)
    matrixPairEquiv K[X] K[X] n m (depthThreeGLColumns M P V T D₀ D₁ D₂ *ᵥ c)=
      (depthThreeReconstructedX M P V (C*T) (C*D₁) (C*D₂),
        depthThreeReconstructedU M V (C*T) (C*D₀) (C*D₁) (C*D₂)) := by
  intro C
  apply Prod.ext
  · funext x y
    change (∑ kj, (V x kj.1*(T*P*(M^2 : Matrix n n K[X])-D₂*(P*M)-D₁*P) kj.2 y+
      (M*V) x kj.1*(T*P*M-D₂*P) kj.2 y+
      ((M^2 : Matrix n n K[X])*V) x kj.1*(T*P) kj.2 y)*c kj)=_
    simp only [add_mul,Finset.sum_add_distrib]
    have he := congrArg₂ (fun a b : K[X] => a+b)
      (congrArg₂ (fun a b : K[X] => a+b)
        (congrFun (tensorColumns_mulVec V (T*P*(M^2 : Matrix n n K[X])-D₂*(P*M)-D₁*P) c) (x,y))
        (congrFun (tensorColumns_mulVec (M*V) (T*P*M-D₂*P) c) (x,y)))
      (congrFun (tensorColumns_mulVec ((M^2 : Matrix n n K[X])*V) (T*P) c) (x,y))
    simpa only [depthThreeReconstructedX,C,Matrix.mul_sub,Matrix.mul_assoc,Matrix.add_apply] using he
  · funext x y
    change (∑ kj, (((M^3 : Matrix n n K[X])*V) x kj.1*T kj.2 y-((M^2 : Matrix n n K[X])*V) x kj.1*D₂ kj.2 y-
      (M*V) x kj.1*D₁ kj.2 y-V x kj.1*D₀ kj.2 y)*c kj)=_
    simp only [sub_mul,Finset.sum_sub_distrib]
    have he := congrArg₂ (fun a b : K[X] => a-b)
      (congrArg₂ (fun a b : K[X] => a-b)
        (congrArg₂ (fun a b : K[X] => a-b)
          (congrFun (tensorColumns_mulVec ((M^3 : Matrix n n K[X])*V) T c) (x,y))
          (congrFun (tensorColumns_mulVec ((M^2 : Matrix n n K[X])*V) D₂ c) (x,y)))
        (congrFun (tensorColumns_mulVec (M*V) D₁ c) (x,y)))
      (congrFun (tensorColumns_mulVec V D₀ c) (x,y))
    simpa only [depthThreeReconstructedU,C,Matrix.mul_assoc,Matrix.sub_apply] using he

def depthThreeGLMap (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (V : Matrix n r K[X]) (T D₀ D₁ D₂ : Matrix s m K[X])
    (hPV : P*V=0) (hPMV : P*M*V=0) (hPMMV : P*(M^2 : Matrix n n K[X])*V=0)
    (hrel : T*P*(M^3 : Matrix n n K[X])=D₀*P+D₁*(P*M)+D₂*(P*(M^2 : Matrix n n K[X]))) :
    (r × s → K[X]) →ₗ[K[X]] LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) :=
  (Matrix.toLin' (depthThreeGLColumns M P V T D₀ D₁ D₂)).codRestrict _ (by
    intro c
    apply (glEquationMatrix_kernel_iff M P _).mpr
    rw [Matrix.toLin'_apply,depthThreeGLColumns_mulVec]
    let C : Matrix r s K[X] := fun i j => c (i,j)
    have hr : (C*T)*P*(M^3 : Matrix n n K[X])=(C*D₀)*P+(C*D₁)*(P*M)+(C*D₂)*(P*(M^2 : Matrix n n K[X])) := by
      have hh := congrArg (fun Y : Matrix s n K[X] => C*Y) hrel
      simpa only [Matrix.mul_add,Matrix.mul_assoc] using hh
    have hh := depth_three_reconstructed_pair_equations M P V (C*T) (C*D₀) (C*D₁) (C*D₂)
      hPV hPMV hPMMV hr
    exact ⟨hh.1,sub_eq_zero.mpr hh.2⟩)

set_option maxHeartbeats 800000 in
theorem depthThreeGLMap_bijective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*(M^3 : Matrix n n K[X])*polynomialKernelBasisMatrix (observabilityMatrix M P 3) Bv).transpose)))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (D₀ D₁ D₂ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*(M^3 : Matrix n n K[X])=
      D₀*P+D₁*(P*M)+D₂*(P*(M^2 : Matrix n n K[X])))
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec)
    (hPV : P*polynomialKernelBasisMatrix _ Bv=0)
    (hPMV : P*M*polynomialKernelBasisMatrix _ Bv=0)
    (hPMMV : P*(M^2 : Matrix n n K[X])*polynomialKernelBasisMatrix _ Bv=0) :
    Function.Bijective (depthThreeGLMap M P (polynomialKernelBasisMatrix _ Bv)
      (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ D₂ hPV hPMV hPMMV hrel) := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P 3) Bv
  let T : Matrix s m K[X] := (polynomialKernelBasisMatrix _ Bt).transpose
  have hV := polynomialKernelBasisMatrix_injective _ Bv
  have hT : Function.Injective T.transpose.mulVec := by
    simpa only [T,Matrix.transpose_transpose] using polynomialKernelBasisMatrix_injective _ Bt
  constructor
  · intro c d h
    have hp := congrArg (fun z : LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) =>
      matrixPairEquiv K[X] K[X] n m z.val) h
    change matrixPairEquiv _ _ _ _ (depthThreeGLColumns M P V T D₀ D₁ D₂ *ᵥ c)=
      matrixPairEquiv _ _ _ _ (depthThreeGLColumns M P V T D₀ D₁ D₂ *ᵥ d) at hp
    rw [depthThreeGLColumns_mulVec,depthThreeGLColumns_mulVec] at hp
    have hx := congrArg Prod.fst hp
    have ht := congrArg (fun Y : Matrix n n K[X] => Y*(Matrix.of fun a b => R a (2,b))) hx
    dsimp only at ht
    rw [depth_three_reconstructed_terminal M P R hR,
      depth_three_reconstructed_terminal M P R hR] at ht
    have he := matrix_left_mul_injective_of_mulVec _ hV ht
    have het := congrArg Matrix.transpose he
    simp only [Matrix.transpose_mul] at het
    have hc := matrix_left_mul_injective_of_mulVec _ hT het
    funext k
    exact congrFun (congrFun hc k.2) k.1
  · intro z
    let X := (matrixPairEquiv K[X] K[X] n m z.val).1
    let U := (matrixPairEquiv K[X] K[X] n m z.val).2
    obtain ⟨hPX,hres⟩ := (glEquationMatrix_kernel_iff M P z.val).mp z.property
    change P*X=0 at hPX
    change M*X-X*M-U*P=0 at hres
    obtain ⟨E,⟨hE,hEF⟩,_⟩ := depth_three_gl_terminal_beta_parameter M P Bv R hR hO X U
      hPX (sub_eq_zero.mp hres)
    have hEt : (P*(M^3 : Matrix n n K[X])*V).transpose*E.transpose=0 := by
      simpa only [Matrix.transpose_mul,Matrix.transpose_zero] using congrArg Matrix.transpose hEF
    obtain ⟨Q,hQ⟩ := matrix_factor_through_kernel_basis _ Bt E.transpose hEt
    have he : E=Q.transpose*T := by
      simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using congrArg Matrix.transpose hQ
    have hr : (Q.transpose*T)*P*(M^3 : Matrix n n K[X])=
        (Q.transpose*D₀)*P+(Q.transpose*D₁)*(P*M)+(Q.transpose*D₂)*(P*(M^2 : Matrix n n K[X])) := by
      have hh := congrArg (fun Y : Matrix s n K[X] => Q.transpose*Y) hrel
      simpa only [T,Matrix.mul_add,Matrix.mul_assoc] using hh
    have hpair := depth_three_gl_reconstruction M P Bv R hR hO X U hPX (sub_eq_zero.mp hres)
      (Q.transpose*T) (Q.transpose*D₀) (Q.transpose*D₁) (Q.transpose*D₂)
      (by simpa only [he] using hE) hr
    let c : r × s → K[X] := fun k => Q k.2 k.1
    refine ⟨c,?_⟩
    apply Subtype.ext
    apply (matrixPairEquiv K[X] K[X] n m).injective
    change matrixPairEquiv _ _ _ _ (depthThreeGLColumns M P V T D₀ D₁ D₂ *ᵥ c)=_
    rw [depthThreeGLColumns_mulVec]
    exact Prod.ext hpair.1.symm hpair.2.symm

def depthThreeGLKernelBasis (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*(M^3 : Matrix n n K[X])*polynomialKernelBasisMatrix (observabilityMatrix M P 3) Bv).transpose)))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (D₀ D₁ D₂ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*(M^3 : Matrix n n K[X])=
      D₀*P+D₁*(P*M)+D₂*(P*(M^2 : Matrix n n K[X])))
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec) :
    Basis (r × s) K[X] (LinearMap.ker (Matrix.toLin' (glEquationMatrix M P))) := by
  have hV (j : ℕ) (hj : j<3) : P*M^j*polynomialKernelBasisMatrix _ Bv=0 := by
    have he := polynomialKernelBasisMatrix_mul (observabilityMatrix M P 3) Bv
    funext i k
    exact congrFun (congrFun he (⟨j,hj⟩,i)) k
  have hPV : P*polynomialKernelBasisMatrix _ Bv=0 := by simpa using hV 0 (by omega)
  have hPMV : P*M*polynomialKernelBasisMatrix _ Bv=0 := by simpa using hV 1 (by omega)
  exact (Pi.basisFun K[X] (r × s)).map (LinearEquiv.ofBijective
    (depthThreeGLMap M P (polynomialKernelBasisMatrix _ Bv)
      (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ D₂ hPV hPMV (hV 2 (by omega)) hrel)
    (depthThreeGLMap_bijective M P Bv Bt R hR D₀ D₁ D₂ hrel hO hPV hPMV (hV 2 (by omega))))

set_option maxHeartbeats 800000 in
theorem polynomialKernelBasisMatrix_depthThreeGL
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P 3))))
    (Bt : Basis s K[X] (LinearMap.ker (Matrix.toLin'
      (P*(M^3 : Matrix n n K[X])*polynomialKernelBasisMatrix (observabilityMatrix M P 3) Bv).transpose)))
    (R : Matrix n (Fin 3 × m) K[X]) (hR : observabilityMatrix M P 3*R=1)
    (D₀ D₁ D₂ : Matrix s m K[X])
    (hrel : (polynomialKernelBasisMatrix _ Bt).transpose*P*(M^3 : Matrix n n K[X])=
      D₀*P+D₁*(P*M)+D₂*(P*(M^2 : Matrix n n K[X])))
    (hO : Function.Injective (observabilityMatrix M P 4).mulVec) :
    polynomialKernelBasisMatrix (glEquationMatrix M P)
      (depthThreeGLKernelBasis M P Bv Bt R hR D₀ D₁ D₂ hrel hO)=
      depthThreeGLColumns M P (polynomialKernelBasisMatrix _ Bv)
        (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ D₂ := by
  funext i j
  change (depthThreeGLColumns M P (polynomialKernelBasisMatrix _ Bv)
    (polynomialKernelBasisMatrix _ Bt).transpose D₀ D₁ D₂ *ᵥ (Pi.basisFun K[X] (r × s) j)) i=_
  simp [Pi.basisFun_apply,Matrix.mulVec_single]

theorem generic_depth_three_gl_kernel_basis
    (hmn : 3*Fintype.card m<Fintype.card n)
    (hnm : Fintype.card n≤4*Fintype.card m)
    (Bv : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3))))
    (Bt : Basis s (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' ((genericAffineRows K n m)*
        (genericAffineSquare K n m)^3*polynomialKernelBasisMatrix _ Bv).transpose))) :
    Nonempty (Basis (r × s) (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m))))) := by
  let M := genericAffineSquare K n m
  let P := genericAffineRows K n m
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P 3) Bv
  let T := (polynomialKernelBasisMatrix _ Bt).transpose
  obtain ⟨R,_,hR⟩ := generic_actual_depth_three_stack_right_inverse (K := K) hmn
  have hTF : T*(P*M^3*V)=0 := by
    have he := polynomialKernelBasisMatrix_mul _ Bt
    simpa only [T,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using
      congrArg Matrix.transpose he
  obtain ⟨D₀,D₁,D₂,hrel⟩ := exists_depth_three_beta_coefficients M P Bv R hR T hTF
  exact ⟨depthThreeGLKernelBasis M P Bv Bt R hR D₀ D₁ D₂ hrel
    (generic_terminal_observability_injective 3 (Nat.le_of_lt hmn) hnm)⟩

end FD56
