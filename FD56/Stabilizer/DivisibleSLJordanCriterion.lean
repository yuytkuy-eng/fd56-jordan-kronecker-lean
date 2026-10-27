/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.DivisibleGLJordanCriterion
import FD56.Stabilizer.DivisibleSLMinimalCriterion
import FD56.Stabilizer.SLCanonicalFromRegularGL
import FD56.Stabilizer.GenericDivisibleGLTrace
import FD56.Hilbert.RankTwoJordanDimension

/-! A concrete observability criterion for the full divisible SL canonical decomposition. -/

noncomputable section
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
namespace FD56
open Matrix Polynomial
variable {K : Type*} {m : Type} [Field K] [IsAlgClosed K] [Fintype m] [DecidableEq m]
local instance divisibleSLJordanCriterionDecidableEq : DecidableEq K := Classical.decEq K

theorem divisible_sl_jordan_of_observability_inverses (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) K[X])
    (P : Matrix m (Fin (q+1) × m) K[X]) (i₀ : Fin (q+1) × m)
    (hm : 2≤Fintype.card m) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (R : Matrix (Fin (q+1) × m) (Fin q × m) K[X])
    (V : Matrix (Fin (q+1) × m) (Fin (q+2) × m) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (hV : V*observabilityMatrix M P (q+2)=1)
    (hs : (observabilityMatrix M P (q+1)).det.Separable)
    (hlead : Matrix.det (fun i j => (glKirillovMatrix M P i j).coeff 1)≠0) :
    let H := glKirillovMatrix M P
    let f := polynomialPencilOperator H
    ∃ T : Matrix (SLChartInput (Fin (q+1) × m) m i₀)
      (rankTwoSLCanonicalIndex (fun _ : f.Eigenvalues => Fintype.card m-2)) K,
    ∃ S : Matrix (rankTwoSLCanonicalIndex (fun _ : f.Eigenvalues => Fintype.card m-2))
      (SLChartInput (Fin (q+1) × m) m i₀) K,
      T*S=1 ∧ S*T=1 ∧ (T.map C).transpose*slKirillovMatrix M P i₀*T.map C=
        rankTwoSLCanonicalTarget (fun a : f.Eigenvalues => a.val) (fun _ => Fintype.card m-2) := by
  classical
  let H := glKirillovMatrix M P
  let f := polynomialPencilOperator H
  obtain ⟨G,J,hGJ,hJG,hcong⟩ := divisible_gl_jordan_of_observability_inverses q M P hm hM hP R V hR hV hs hlead
  have hcount : Fintype.card f.Eigenvalues=Fintype.card m*(q+1)*(q+2)/2 :=
    divisible_rank_two_basis_pole_count q hm G J hGJ hJG
  have htwo : 2≤(q+1)*(q+2) := by nlinarith
  have hprod : 2*Fintype.card m≤Fintype.card m*(q+1)*(q+2) := by nlinarith
  letI : Nontrivial f.Eigenvalues := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let a₀ : f.Eigenvalues := Classical.choice inferInstance
  have hmin : HasMinimalKernelDegrees (slKirillovMatrix M P i₀) [Fintype.card f.Eigenvalues-1] := by
    rw [hcount]
    exact (slKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _ _).mpr
      (divisible_sl_minimal_degrees_of_observability q M P i₀ hM hP hs hlead)
  apply sl_canonical_of_rank_two_gl_and_maximal_index M P i₀
    (fun a : f.Eigenvalues => a.val) Subtype.val_injective (Fintype.card m-2) a₀
    G J hGJ hJG hcong _ hmin
  intro a v hv
  let ev := Polynomial.evalRingHom a.val
  have hleft : V.map ev*observabilityMatrix (M.map ev) (P.map ev) (q+2)=1 := by
    have h := congrArg (fun Z => Z.map ev) hV
    simpa only [Matrix.map_mul,observabilityMatrix_map,
      Matrix.map_one _ (map_zero ev) (map_one ev)] using h
  have hinj : Function.Injective (observabilityMatrix (M.map ev) (P.map ev) (q+2)).mulVec := by
    intro u w huw
    have h := congrArg (V.map ev).mulVec huw
    simpa only [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec] using h
  have hn : Module.finrank K (unobservableSpace (M.map ev) (P.map ev) (q+2))=0 := by
    rw [← observabilityMatrix_ker,LinearMap.ker_eq_bot.mpr hinj,finrank_bot]
  apply observable_gl_kirillov_kernel_trace_zero (M.map ev) (P.map ev) (q+2) hn v
  simpa only [glKirillovMatrix_map] using hv

end FD56
