/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenFourSLData

/-! A small integer left-inverse certificate verifies the leading rank. -/
noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def tenFourLeadingData : Matrix (Fin 140) (Fin 5) (List ℤ) :=
  fun i j => [(tenFourZData i j).getD (tenFourDegrees j) 0]

private theorem tenFour_leading_certificate : ∀ i j : Fin 5,
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeadingLeftData tenFourLeadingData i j)=
      integerPolynomialTrim (if i=j then [tenFourLeadingScale] else []) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem tenFour_leading_injective [CharZero K] :
    Function.Injective (Matrix.mulVec
      (fun i j => (tenFourZ (K:=K) i j).coeff (tenFourDegrees j))) := by
  let L := (integerPolynomialMatrix (K:=K) tenFourLeadingLeftData).map (Polynomial.evalRingHom 0)
  let G : Matrix (Fin 140) (Fin 5) K :=
    fun i j => (tenFourZRaw (K:=K) i j).coeff (tenFourDegrees j)
  have hp := integerPolynomialMatrix_mul_of_trim_eq (K:=K) tenFourLeadingLeftData tenFourLeadingData
    (fun i j => if i=j then [tenFourLeadingScale] else []) tenFour_leading_certificate
  have he : (integerPolynomialMatrix (K:=K) tenFourLeadingData).map (Polynomial.evalRingHom 0)=G := by
    funext i j
    simp [G,tenFourLeadingData,tenFourZRaw,integerPolynomialMatrix,integerPolynomial_coeff]
  have hL : L*G=(tenFourLeadingScale : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
    have h := congrArg (fun A => A.map (Polynomial.evalRingHom (0 : K))) hp
    dsimp only at h
    rw [Matrix.map_mul,he] at h
    refine h.trans ?_
    funext i j
    by_cases hij : i=j <;>
      simp [integerPolynomialMatrix,hij,Matrix.map_apply,Matrix.smul_apply,Matrix.one_apply]
  have hD : (tenFourLeadingScale : K)≠0 := by
    exact_mod_cast (by norm_num [tenFourLeadingScale] : tenFourLeadingScale≠0)
  intro v w hv
  have hg : G*ᵥv=G*ᵥw := by
    funext i
    have h := congrFun hv (tenFourInputEquiv.symm i)
    simpa [G,tenFourZ,Matrix.mulVec,Matrix.submatrix_apply] using h
  have hh := congrArg (fun x => L*ᵥx) hg
  dsimp only at hh
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hL] at hh
  funext j
  have he := congrFun hh j
  apply mul_left_cancel₀ hD
  simpa only [Matrix.smul_mulVec_assoc,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul] using he

end FD56
