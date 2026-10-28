/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerScalarForcing
import FD56.Hilbert.MixedGLKronecker
import FD56.Hilbert.GenericObservableSLHilbert
import FD56.Hilbert.SLScalarCrossVanishing

/-! A pure GL Kronecker decomposition gives eventual scalar surjectivity for
the actual SL restriction whenever every GL stabilizer is traceless. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def glKirillovTraceVector : SLInput n m → K :=
  Sum.elim (fun ij => (1 : Matrix n n K) ij.1 ij.2) (fun _ => 0)

theorem glKirillovTraceVector_dot (v : SLInput n m → K[X]) :
    (fun k => C (glKirillovTraceVector (K:=K) (n:=n) (m:=m) k)) ⬝ᵥ v=
      Matrix.trace (matrixPairEquiv K[X] K[X] n m v).1 := by
  simp [glKirillovTraceVector,dotProduct,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Matrix.one_apply,Matrix.trace,Matrix.diag,matrixPairEquiv]

theorem glKirillovMatrix_scalar_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (v : SLInput n m → K[X]) (c : K[X]) :
    glKirillovMatrix M P *ᵥ v=
      c • (fun k => C (glKirillovTraceVector (K:=K) (n:=n) (m:=m) k)) ↔
      P*(matrixPairEquiv K[X] K[X] n m v).1=0 ∧
      stabilizerResidual M P (matrixPairEquiv K[X] K[X] n m v)=c • 1 := by
  rw [glKirillovMatrix_mulVec]
  constructor
  · intro h
    constructor
    · funext i j
      simpa [glKirillovTraceVector] using congrFun h (.inr (j,i))
    · funext i j
      simpa [glKirillovTraceVector,Matrix.one_apply,eq_comm] using congrFun h (.inl (j,i))
  · rintro ⟨hP,hres⟩
    funext k
    rcases k with ⟨i,j⟩|⟨i,j⟩ <;>
      simp [hP,hres,glKirillovTraceVector,Matrix.one_apply,eq_comm]

theorem slHilbert_high_of_gl_kronecker
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n)
    (xs : List ℕ) (hGL : HasKroneckerDecomposition (glKirillovMatrix M P) xs)
    (htrace : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      P*X=0 → M*X-X*M=U*P → Matrix.trace X=0)
    (d : ℕ) (hd : ∀ e ∈ xs, e≤d+1) :
    slHilbert M P d=
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d)+(d+2) := by
  letI : Nonempty n := ⟨i₀⟩
  obtain ⟨r,e,hperm,T,S,hTS,hST,hcong⟩ := hGL
  apply slHilbert_eq_gl_add_of_scalar_lifts M P hM hP i₀ d htrace
  intro c hc
  have ha : ∀ v : SLInput n m → K[X], glKirillovMatrix M P *ᵥ v=0 →
      (fun k => C (glKirillovTraceVector (K:=K) (n:=n) (m:=m) k)) ⬝ᵥ v=0 := by
    intro v hv
    have hh := (glKirillovMatrix_scalar_iff M P v 0).mp (by simpa using hv)
    rw [glKirillovTraceVector_dot]
    apply htrace _ _ hh.1
    have hres := hh.2
    change M*(matrixPairEquiv K[X] K[X] n m v).1-
      (matrixPairEquiv K[X] K[X] n m v).1*M-
      (matrixPairEquiv K[X] K[X] n m v).2*P=0 • (1 : Matrix n n K[X]) at hres
    simpa only [zero_smul,sub_eq_zero] using hres
  have he : ∀ j, e j≤d+1 := by
    intro j
    apply hd
    exact hperm.mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩)
  obtain ⟨v,hv,hforce,hzero⟩ := constant_congruence_scalar_forcing_lift
    (glKirillovMatrix M P) e T S hTS hST hcong glKirillovTraceVector ha d he c hc
  have hh := (glKirillovMatrix_scalar_iff M P v c).mp hforce
  let X := (matrixPairEquiv K[X] K[X] n m v).1
  let U := (matrixPairEquiv K[X] K[X] n m v).2
  have htr : Matrix.trace X=0 := (glKirillovTraceVector_dot v).symm.trans hzero
  have hp : P*X=0 := hh.1
  have hcomm : M*X-X*M=U*P+c • 1 := by
    have hres := hh.2
    change M*X-X*M-U*P=c • (1 : Matrix n n K[X]) at hres
    exact (sub_eq_iff_eq_add.mp hres).trans (add_comm _ _)
  exact ⟨X,U,(fun i j => hv (.inl (i,j))),(fun i j => hv (.inr (i,j))),
    (slRadical_iff_equations M P X U).mpr ⟨htr,hp,c,hcomm⟩,hcomm⟩

theorem generic_slHilbert_high_of_gl_kronecker
    (hm : 0<Fintype.card m) (i₀ : n) (xs : List ℕ)
    (hGL : HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) xs)
    (d : ℕ) (hd : ∀ e ∈ xs, e≤d+1) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d=
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m)) d)+(d+2) := by
  apply slHilbert_high_of_gl_kronecker _ _ (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) i₀ xs hGL _ d hd
  intro X U hPX hcomm
  exact generic_scalar_commutator_trace_zero hm X U 0 hPX (by simpa using hcomm)

end FD56
