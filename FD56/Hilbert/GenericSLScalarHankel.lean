/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ConstantKroneckerScalarObstruction
import FD56.Hilbert.KroneckerSLHilbert
import FD56.Hilbert.GenericGLClassification

/-! The actual generic SL scalar image is the kernel of the Hankel
obstruction of its transformed trace covector. No maximal-rank claim is
made for that covector. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 1000000

theorem boundedSLScalar_mem_range_iff_forcing
    {K n m : Type*} [Field K] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (c : BoundedPoly K (d+1)) :
    c∈LinearMap.range (boundedSLScalar M P hM hP i₀ d) ↔
    ∃ z : SLInput n m → K[X], (∀ k, (z k).natDegree≤d) ∧
      glKirillovMatrix M P *ᵥ z=c.val • (fun k => C (glKirillovTraceVector (n:=n) (m:=m) k)) ∧
      (fun k => C (glKirillovTraceVector (n:=n) (m:=m) k)) ⬝ᵥ z=0 := by
  letI : Nonempty n := ⟨i₀⟩
  constructor
  · rintro ⟨v,hv⟩
    let z := (matrixPairEquiv K[X] K[X] n m).symm (entries v.val.1,entries v.val.2)
    obtain ⟨htrace,hPX,_⟩ := (slRadical_iff_equations M P _ _).mp v.property
    have hres := boundedSLScalar_residual M P hM hP i₀ d v
    rw [hv] at hres
    refine ⟨z,?_,?_,?_⟩
    · intro k
      rcases k with ⟨i,j⟩|⟨i,j⟩
      · exact entries_degree v.val.1 i j
      · exact entries_degree v.val.2 i j
    · apply (glKirillovMatrix_scalar_iff M P z c.val).mpr
      simpa only [z,LinearEquiv.apply_symm_apply] using And.intro hPX hres
    · rw [glKirillovTraceVector_dot]
      simpa only [z,LinearEquiv.apply_symm_apply] using htrace
  · rintro ⟨z,hz,hforce,hzero⟩
    let X := (matrixPairEquiv K[X] K[X] n m z).1
    let U := (matrixPairEquiv K[X] K[X] n m z).2
    have hX : DegreeBound X d := fun i j => hz (.inl (i,j))
    have hU : DegreeBound U d := fun i j => hz (.inr (i,j))
    obtain ⟨hPX,hres⟩ := (glKirillovMatrix_scalar_iff M P z c.val).mp hforce
    have htrace : Matrix.trace X=0 := (glKirillovTraceVector_dot z).symm.trans hzero
    have hcomm : M*X-X*M=U*P+c.val • 1 := by
      change M*X-X*M-U*P=c.val • 1 at hres
      exact (sub_eq_iff_eq_add.mp hres).trans (add_comm _ _)
    have hs : SLRadical M P X U :=
      (slRadical_iff_equations M P X U).mpr ⟨htrace,hPX,c.val,hcomm⟩
    refine ⟨⟨(boundedMatrixOf X hX,boundedMatrixOf U hU),hs⟩,?_⟩
    apply Subtype.ext
    change (M*X-X*M-U*P) i₀ i₀=c.val
    rw [hcomm,add_sub_cancel_left]
    simp

private theorem trace_covector_annihilates_gl_kernel
    {L n m : Type*} [Field L] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (htrace : ∀ X U, P*X=0 → M*X-X*M=U*P → Matrix.trace X=0)
    (v : SLInput n m → L[X]) (hv : glKirillovMatrix M P *ᵥ v=0) :
    (fun k => C (glKirillovTraceVector (K:=L) (n:=n) (m:=m) k)) ⬝ᵥ v=0 := by
  have h := (glKirillovMatrix_scalar_iff M P v 0).mp (by simpa using hv)
  rw [glKirillovTraceVector_dot]
  apply htrace _ _ h.1
  have hres := h.2
  change M*(matrixPairEquiv L[X] L[X] n m v).1-
    (matrixPairEquiv L[X] L[X] n m v).1*M-
    (matrixPairEquiv L[X] L[X] n m v).2*P=0 • 1 at hres
  simpa only [zero_smul,sub_eq_zero] using hres

theorem generic_sl_scalar_range_hankel
    {K : Type*} [Field K] (n m : ℕ) (hm : 0<m) (hrem : n%m≠0) (i₀ : Fin n) :
    ∃ (r : ℕ) (e : Fin r → ℕ)
      (a : (Σ i, Fin (e i) ⊕ Fin (e i+1)) →
        AffineCoefficientField K (MatrixParameters (Fin n) (Fin m))),
      (List.ofFn e).Perm (glFormula n m) ∧
      ∀ d, LinearMap.range (boundedSLScalar
        (genericAffineSquare K (Fin n) (Fin m)) (genericAffineRows K (Fin n) (Fin m))
        (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) i₀ d)=
        LinearMap.ker (kroneckerScalarObstruction e a d) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin n) (Fin m))
  let M := genericAffineSquare K (Fin n) (Fin m)
  let P := genericAffineRows K (Fin n) (Fin m)
  let H := glKirillovMatrix M P
  let t := glKirillovTraceVector (K:=L) (n:=Fin n) (m:=Fin m)
  obtain ⟨r,e,hperm,T,S,hTS,hST,hcong⟩ := (generic_nondivisible_gl_formula (K:=K) n m hm hrem).2
  let a := T.transpose *ᵥ t
  have htc : (fun k => C (a k))=(T.map C).transpose *ᵥ (fun k => C (t k)) := by
    ext k
    simp [a,Matrix.mulVec,dotProduct,map_sum,map_mul]
  have hTS' : T.map C*S.map C=1 := by rw [← Matrix.map_mul,hTS]; simp
  have hleft : (S.map C).transpose*(T.map C).transpose=1 := by
    rw [← Matrix.transpose_mul,hTS',Matrix.transpose_one]
  have hinj : Function.Injective (T.map C).transpose.mulVec := by
    intro u v huv
    have h := congrArg (S.map C).transpose.mulVec huv
    simpa only [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec] using h
  have htrace (v : SLInput (Fin n) (Fin m) → L[X]) (hv : H *ᵥ v=0) :
      (fun k => C (t k)) ⬝ᵥ v=0 := by
    apply trace_covector_annihilates_gl_kernel M P _ v hv
    intro X U hPX hcomm
    exact generic_scalar_commutator_trace_zero (K:=K) (by simpa using hm) X U 0 hPX
      (by simpa only [zero_smul,add_zero] using hcomm)
  have ha : ∀ i j, a ⟨i,Sum.inr j⟩=0 := by
    apply kronecker_covector_large_coordinates_zero e a
    intro v hv
    have hz : H *ᵥ (T.map C *ᵥ v)=0 := by
      apply hinj
      rw [Matrix.mulVec_zero]
      simpa only [← hcong,← Matrix.mulVec_mulVec] using hv
    have ht := htrace _ hz
    rw [htc,dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]
    exact ht
  refine ⟨r,e,a,hperm,?_⟩
  intro d
  ext c
  rw [boundedSLScalar_mem_range_iff_forcing]
  exact constant_congruence_scalar_forcing_iff H e T S hTS hST hcong t ha d c

end FD56
