/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.DivisibleObservabilityCertificate
import FD56.Stabilizer.GLObservabilityDeterminant
import FD56.Stabilizer.GenericDivisibleGLPrimary
import FD56.Hilbert.PolynomialRegularRankTwoJordan

/-! A concrete observability criterion for the full divisible GL Jordan decomposition. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem separable_power_root_order (p : K[X]) (hp : p.Separable)
    (x : K) (hx : p.eval x=0) (k : ℕ) : rootMultiplicity x (p^k)=k := by
  have hroot : rootMultiplicity x p=1 := by
    have hle := rootMultiplicity_le_one_of_separable hp x
    have hpos := (Polynomial.rootMultiplicity_pos hp.ne_zero).mpr hx
    omega
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hp.ne_zero) hp.ne_zero),ih,hroot]

variable {m : Type} [Fintype m] [DecidableEq m] [IsAlgClosed K]
local instance divisibleGLJordanCriterionDecidableEq : DecidableEq K := Classical.decEq K

theorem divisible_gl_jordan_of_observability_inverses (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) K[X])
    (P : Matrix m (Fin (q+1) × m) K[X])
    (hm : 2≤Fintype.card m) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (R : Matrix (Fin (q+1) × m) (Fin q × m) K[X])
    (V : Matrix (Fin (q+1) × m) (Fin (q+2) × m) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (hV : V*observabilityMatrix M P (q+2)=1)
    (hs : (observabilityMatrix M P (q+1)).det.Separable)
    (hlead : Matrix.det (fun i j => (glKirillovMatrix M P i j).coeff 1)≠0) :
    let H := glKirillovMatrix M P
    let f := polynomialPencilOperator H
    ∃ T : Matrix (SLInput (Fin (q+1) × m) m)
      (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2)) K,
    ∃ S : Matrix (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2))
      (SLInput (Fin (q+1) × m) m) K,
      T*S=1 ∧ S*T=1 ∧ (T.map C).transpose*H*T.map C=
        Matrix.blockDiagonal' (fun a : f.Eigenvalues => rankTwoJordanPencil a.val (Fintype.card m-2)) := by
  classical
  let H := glKirillovMatrix M P
  have hH : DegreeBound H 1 := glKirillovMatrix_degreeBound M P 1 hM hP
  have hdet : H.det=(observabilityMatrix M P (q+1)).det^(2*Fintype.card m) :=
    glKirillovMatrix_det_observability_ne_zero q M P hs.ne_zero
  apply polynomial_regular_rank_two_jordan_decomposition H hH
    (glKirillovMatrix_coefficient_alternating M P 0)
    (glKirillovMatrix_coefficient_alternating M P 1) hlead (Fintype.card m)
  intro x hx
  have hxO : (observabilityMatrix M P (q+1)).det.eval x=0 := by
    rw [hdet,Polynomial.eval_pow] at hx
    exact pow_eq_zero hx
  obtain ⟨hb,hf,hn⟩ := divisible_observability_inverse_root_profile q M P R V hR hV hs
    (RingHom.id K) x hxO
  have hk : Module.finrank K (LinearMap.ker (Matrix.toLin' (H.map (Polynomial.evalRingHom x))))=
      2*Fintype.card m-2 := by
    change Module.finrank K (LinearMap.ker (Matrix.toLin'
      ((glKirillovMatrix M P).map (Polynomial.evalRingHom x))))=_
    rw [glKirillovMatrix_map]
    exact glKirillovMatrix_simple_observability_defect_nullity q _ _ hm (by simp) hb hf hn
  have ho : rootMultiplicity x H.det=2*Fintype.card m := by
    rw [hdet]
    exact separable_power_root_order _ hs x hxO _
  obtain ⟨hd,_,hr⟩ := polynomial_pencil_primary_rank_two H hH hlead x (Fintype.card m) (by omega) ho hk
  exact ⟨hd,hr⟩

end FD56
