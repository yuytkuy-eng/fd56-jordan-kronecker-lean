/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenFourSLColumn0
import FD56.Hilbert.TenFourSLColumn1
import FD56.Hilbert.TenFourSLColumn2
import FD56.Hilbert.TenFourSLColumn3
import FD56.Hilbert.TenFourSLColumn4

/-! Integer polynomial identities certify a mixed reduced SL kernel frame. -/
noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem tenFour_trace_certificate : ∀ j : Fin 5,
    integerPolynomialTrim ((List.ofFn (fun i : Fin 10 => tenFourXData j i i)).foldr
      integerPolynomialAdd [])=[] := by
  intro j
  fin_cases j
  · exact tenFour_integer_column0.1
  · exact tenFour_integer_column1.1
  · exact tenFour_integer_column2.1
  · exact tenFour_integer_column3.1
  · exact tenFour_integer_column4.1

private theorem tenFour_PX_certificate : ∀ (j : Fin 5) (a : Fin 4) (b : Fin 10),
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourPData (tenFourXData j) a b)=[] := by
  intro j
  fin_cases j
  · exact tenFour_integer_column0.2.1
  · exact tenFour_integer_column1.2.1
  · exact tenFour_integer_column2.2.1
  · exact tenFour_integer_column3.2.1
  · exact tenFour_integer_column4.2.1

private theorem tenFour_commutator_certificate : ∀ (j : Fin 5) (a b : Fin 10),
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourMData (tenFourXData j) a b)=
      integerPolynomialTrim (integerPolynomialAdd
        (integerPolynomialMatrixProduct (tenFourXData j) tenFourMData a b)
        (integerPolynomialAdd (integerPolynomialMatrixProduct (tenFourUData j) tenFourPData a b)
          (if a=b then tenFourScalarData j else []))) := by
  intro j
  fin_cases j
  · exact tenFour_integer_column0.2.2
  · exact tenFour_integer_column1.2.2
  · exact tenFour_integer_column2.2.2
  · exact tenFour_integer_column3.2.2
  · exact tenFour_integer_column4.2.2

theorem tenFour_SL_kernel (i₀ : Fin 10) :
    (slEquationMatrix (tenFourM (K:=K)) (tenFourP (K:=K)) i₀*tenFourZ (K:=K) :
      Matrix (SLOutput (Fin 10) (Fin 4)) (Fin 5) K[X])=0 := by
  funext k j
  have htrace : Matrix.trace (integerPolynomialMatrix (K:=K) (tenFourXData j))=0 := by
    have h := integerPolynomial_eq_of_trim_eq (K:=K) (bs:=[]) (tenFour_trace_certificate j)
    rw [integerPolynomial_fold_add,List.map_ofFn,List.sum_ofFn] at h
    exact h
  have hPX : (tenFourP (K:=K)*integerPolynomialMatrix (K:=K) (tenFourXData j) :
      Matrix (Fin 4) (Fin 10) K[X])=0 := by
    exact integerPolynomialMatrix_mul_of_trim_eq tenFourPData (tenFourXData j)
      (fun _ _ => []) (tenFour_PX_certificate j)
  have hcomm : tenFourM (K:=K)*integerPolynomialMatrix (K:=K) (tenFourXData j)=
      integerPolynomialMatrix (K:=K) (tenFourXData j)*tenFourM (K:=K)+
        integerPolynomialMatrix (K:=K) (tenFourUData j)*tenFourP (K:=K)+
          integerPolynomial (K:=K) (tenFourScalarData j) • (1 : Matrix (Fin 10) (Fin 10) K[X]) := by
    funext a b
    have h := integerPolynomial_eq_of_trim_eq (K:=K) (tenFour_commutator_certificate j a b)
    rw [integerPolynomial_add,integerPolynomial_add] at h
    change (integerPolynomialMatrix (integerPolynomialMatrixProduct tenFourMData (tenFourXData j))) a b=
      (integerPolynomialMatrix (integerPolynomialMatrixProduct (tenFourXData j) tenFourMData)) a b+
        ((integerPolynomialMatrix (integerPolynomialMatrixProduct (tenFourUData j) tenFourPData)) a b+
          integerPolynomial (if a=b then tenFourScalarData j else [])) at h
    rw [integerPolynomialMatrix_product,integerPolynomialMatrix_product,
      integerPolynomialMatrix_product] at h
    by_cases hab : a=b <;>
      simpa [tenFourM,tenFourP,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,hab,add_assoc] using h
  have hz : slEquationMatrix (tenFourM (K:=K)) tenFourP i₀ *ᵥ (fun a => tenFourZ a j)=0 := by
    apply (slEquationMatrix_kernel_iff _ _ _ _).mpr
    apply (slRadical_iff_equations _ _ _ _).mpr
    refine ⟨htrace,hPX,integerPolynomial (tenFourScalarData j),?_⟩
    change tenFourM*integerPolynomialMatrix (tenFourXData j)-
      integerPolynomialMatrix (tenFourXData j)*tenFourM=
        integerPolynomialMatrix (tenFourUData j)*tenFourP+_
    rw [hcomm]
    abel
  exact congrFun hz k

end FD56
