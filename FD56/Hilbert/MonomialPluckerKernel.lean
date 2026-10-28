/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.CofactorKernelComplement
import FD56.LinearAlgebra.ExactKernelBasis
import FD56.Hilbert.MinimalProfile
import Mathlib.LinearAlgebra.Matrix.Block

/-! A primitive monomial Plucker row with an explicit reduced bidiagonal kernel basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def monomialPluckerRow (a b c : ℕ) : Fin 6 → K[X] :=
  ![1, X^a, X^(a+b), X^(a+b+c), 2*X^(a+2*b+c), X^(2*a+2*b+c)]

def monomialPluckerDegrees (a b c : ℕ) : Fin 5 → ℕ := ![a,b,c,b,a]

def monomialPluckerFrame (a b c : ℕ) : Matrix (Fin 6) (Fin 5) K[X] :=
  ![![X^a,0,0,0,0],
    ![-1,X^b,0,0,0],
    ![0,-1,X^c,0,0],
    ![0,0,-1,2*X^b,0],
    ![0,0,0,-1,X^a],
    ![0,0,0,0,-2]]

omit [CharZero K] in
theorem monomialPlucker_relation (a b c : ℕ) :
    monomialPluckerRow (K:=K) a b c 0 * monomialPluckerRow (K:=K) a b c 5 -
      monomialPluckerRow (K:=K) a b c 1 * monomialPluckerRow (K:=K) a b c 4 +
      monomialPluckerRow (K:=K) a b c 2 * monomialPluckerRow (K:=K) a b c 3 = 0 := by
  simp [monomialPluckerRow, pow_add, pow_mul]
  ring

omit [CharZero K] in
theorem monomialPlucker_frame_kernel (a b c : ℕ) :
    ((show Matrix Unit (Fin 6) K[X] from fun _ => monomialPluckerRow (K:=K) a b c) * monomialPluckerFrame (K:=K) a b c :
      Matrix Unit (Fin 5) K[X]) = 0 := by
  funext i j
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, monomialPluckerRow,
      monomialPluckerFrame, pow_add, pow_mul] <;> ring

private theorem monomialPlucker_completion_unit (a b c : ℕ) :
    IsUnit (cofactorCompletion (monomialPluckerFrame (K:=K) a b c)
      (Pi.single (0 : Fin 6) 1)).det := by
  have ht : (cofactorCompletion (monomialPluckerFrame (K:=K) a b c)
      (Pi.single (0 : Fin 6) 1)).BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [id_eq, Fin.lt_def] at hij <;> rfl
  rw [Matrix.det_of_upperTriangular ht]
  norm_num [Fin.prod_univ_succ, cofactorCompletion, monomialPluckerFrame, Pi.single_apply, Fin.cases]
  change IsUnit (Polynomial.C (2 : K))
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K) ≠ 0)).map Polynomial.C

theorem monomialPlucker_kernel_coordinates (a b c : ℕ) (x : Fin 6 → K[X]) :
    (fun _ : Unit => monomialPluckerRow (K:=K) a b c) *ᵥ x = 0 ↔
      ∃! v : Fin 5 → K[X], x = monomialPluckerFrame (K:=K) a b c *ᵥ v := by
  let Z : Matrix (Fin 6) (Fin 5) K[X] := monomialPluckerFrame (K:=K) a b c
  let U : Matrix (Fin 6) (Fin 6) K[X] := cofactorCompletion Z (Pi.single (0 : Fin 6) 1)
  have hud : IsUnit U.det := by
    dsimp only [U,Z]
    exact monomialPlucker_completion_unit (K:=K) a b c
  have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr hud
  have hi := Matrix.mulVec_injective_of_isUnit hu
  have htail (v : Fin 5 → K[X]) : U *ᵥ Fin.cases 0 v = Z *ᵥ v := by
    funext i
    simp [U, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cofactorCompletion]
  have hZi : Function.Injective Z.mulVec := by
    intro v w hvw
    have h := hi ((htail v).trans (hvw.trans (htail w).symm))
    exact funext fun j => congrFun h j.succ
  have hrow : monomialPluckerRow (K:=K) a b c ᵥ* U = Pi.single (0 : Fin 6) 1 := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [U, cofactorCompletion, Matrix.vecMul, dotProduct,
        monomialPluckerRow, Fin.sum_univ_succ, Pi.single_apply]
    · exact congrArg (fun B => B () j) (monomialPlucker_frame_kernel (K:=K) a b c)
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) x
    have hz : v 0 = 0 := by
      have hh := congrFun hx ()
      change monomialPluckerRow (K:=K) a b c ⬝ᵥ x = 0 at hh
      rw [← hv, dotProduct_mulVec, hrow] at hh
      simpa [dotProduct, Fin.sum_univ_succ, Pi.single_apply] using hh
    refine ⟨fun j => v j.succ, ?_, ?_⟩
    · rw [← hv]
      funext i
      simp [U, Z, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cofactorCompletion, hz]
    · intro w hw
      apply hZi
      rw [← hw]
      rw [← hv]
      funext i
      simp [U, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cofactorCompletion, hz]
  · rintro ⟨v,rfl,_⟩
    rw [Matrix.mulVec_mulVec, monomialPlucker_frame_kernel, Matrix.zero_mulVec]

theorem monomialPlucker_column_degrees (a b c : ℕ) :
    ∀ i j, (monomialPluckerFrame (K:=K) a b c i j).natDegree ≤ monomialPluckerDegrees a b c j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [monomialPluckerFrame, monomialPluckerDegrees]

theorem monomialPlucker_leading_injective (a b c : ℕ) :
    Function.Injective (Matrix.mulVec (fun i j =>
      (monomialPluckerFrame (K:=K) a b c i j).coeff (monomialPluckerDegrees a b c j))) := by
  intro v w hvw
  have h0 := congrFun hvw (0 : Fin 6)
  have h1 := congrFun hvw (1 : Fin 6)
  have h2 := congrFun hvw (2 : Fin 6)
  have h3 := congrFun hvw (3 : Fin 6)
  have h4 := congrFun hvw (4 : Fin 6)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    monomialPluckerFrame, monomialPluckerDegrees] at h0 h1 h2 h3 h4
  have hv0 : v 0 = w 0 := by simpa using h0
  have hv1 : v 1 = w 1 := by simpa [hv0] using h1
  have hv2 : v 2 = w 2 := by simpa [hv1] using h2
  have hv3 : v 3 = w 3 := by
    have hh : (2 : K) * v 3 = 2 * w 3 := by simpa [hv2] using h3
    exact mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) hh
  have hv4 : v 4 = w 4 := by simpa [hv3] using h4
  funext j
  fin_cases j
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hv4

theorem monomialPlucker_minimal_degrees (a b c : ℕ) :
    HasMinimalKernelDegrees (fun _ : Unit => monomialPluckerRow (K:=K) a b c)
      [a,b,c,b,a] := by
  obtain ⟨B,hB⟩ := kernel_basis_of_unique_coordinates
    (fun _ : Unit => monomialPluckerRow (K:=K) a b c) (monomialPluckerFrame (K:=K) a b c)
    (monomialPlucker_kernel_coordinates a b c)
  have he : polynomialKernelBasisMatrix (fun _ : Unit => monomialPluckerRow (K:=K) a b c) B =
      monomialPluckerFrame (K:=K) a b c := funext fun i => funext fun j => hB i j
  refine ⟨5,B,monomialPluckerDegrees a b c,?_,?_,?_⟩
  · rw [he]
    exact monomialPlucker_column_degrees a b c
  · rw [he]
    exact monomialPlucker_leading_injective a b c
  · simp [monomialPluckerDegrees, List.ofFn_succ]

end FD56
