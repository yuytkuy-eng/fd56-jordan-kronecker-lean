/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.CongruenceSpecialization
import Mathlib.Algebra.MvPolynomial.Funext

/-! A rational constant congruence holds on a nonempty principal locus over an infinite field. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K F σ n b : Type*} [Field K] [Field F]
  [Fintype n] [Fintype b] [DecidableEq n] [DecidableEq b]

omit [Fintype b] [DecidableEq n] [DecidableEq b] in
theorem polynomial_constant_congruence_coefficients
    (A : Matrix n n K[X]) (T : Matrix n b K) (k : ℕ) :
    (fun i j => (((T.map C).transpose * A * T.map C) i j).coeff k) =
      T.transpose * (Matrix.of fun i j => (A i j).coeff k) * T := by
  ext i j
  simp [Matrix.mul_apply, Polynomial.coeff_sum, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_C]

variable [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]

theorem polynomial_congruence_principal_specialization
    (A : Matrix n n (MvPolynomial σ K)[X]) (B : Matrix b b K[X])
    (T : Matrix n b F) (S : Matrix b n F)
    (hTS : T*S=1) (hST : S*T=1)
    (hform : (T.map C).transpose *
      A.map (Polynomial.mapRingHom (algebraMap (MvPolynomial σ K) F)) * T.map C =
      B.map (Polynomial.mapRingHom
        ((algebraMap (MvPolynomial σ K) F).comp MvPolynomial.C))) :
    ∃ δ : MvPolynomial σ K, δ ≠ 0 ∧
      ∀ x : σ → K, MvPolynomial.eval x δ ≠ 0 →
      ∃ (U : Matrix n b K) (V : Matrix b n K), U*V=1 ∧ V*U=1 ∧
        (U.map C).transpose * A.map (Polynomial.mapRingHom (MvPolynomial.eval x)) *
          U.map C = B := by
  let AR : ℕ → Matrix n n (MvPolynomial σ K) := fun k i j => (A i j).coeff k
  let BR : ℕ → Matrix b b (MvPolynomial σ K) :=
    fun k i j => MvPolynomial.C ((B i j).coeff k)
  have hc (k : ℕ) : T.transpose * (AR k).map (algebraMap (MvPolynomial σ K) F) * T =
      (BR k).map (algebraMap (MvPolynomial σ K) F) := by
    have h := congrArg (fun M : Matrix b b F[X] => fun i j => (M i j).coeff k) hform
    dsimp only at h
    rw [polynomial_constant_congruence_coefficients] at h
    simpa only [AR,BR,Matrix.map_apply,Polynomial.coe_mapRingHom,
      Polynomial.coeff_map,RingHom.coe_comp,Function.comp_apply,Matrix.of_apply] using h
  obtain ⟨δ,U,V,hδ,hUV,hVU,hc⟩ :=
    simultaneous_congruence_clear_denominators AR BR T S hTS hST hc
  refine ⟨δ,hδ,?_⟩
  intro x hx
  obtain ⟨U',V',hUV',hVU',hc'⟩ :=
    simultaneous_congruence_specialize_certificate AR BR δ U V hUV hVU hc
      (MvPolynomial.eval x) hx
  refine ⟨U',V',hUV',hVU',?_⟩
  ext i j k
  have h := congrFun (congrFun (hc' k) i) j
  have hcoeff := congrFun (congrFun (polynomial_constant_congruence_coefficients
    (A.map (Polynomial.mapRingHom (MvPolynomial.eval x))) U' k) i) j
  rw [hcoeff]
  simpa only [AR,BR,Matrix.map_apply,Polynomial.coe_mapRingHom,Polynomial.coeff_map,
    MvPolynomial.eval_C,Matrix.of_apply] using h

theorem nonzero_polynomial_has_nonzero_evaluation [Infinite K]
    (δ : MvPolynomial σ K) (hδ : δ ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x δ ≠ 0 := by
  by_contra h
  push_neg at h
  apply hδ
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

end FD56
