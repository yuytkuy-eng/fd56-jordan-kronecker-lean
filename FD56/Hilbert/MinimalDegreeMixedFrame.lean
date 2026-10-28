/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalDegreeFrameBound
import Mathlib.Data.List.FinRange

/-! A full kernel frame with sharp total degree determines every minimal index,
even when its column degrees differ. Independence at one point suffices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

theorem minimal_degrees_of_full_mixed_frame_at_point
    (A : Matrix a b K[X]) (xs : List ℕ) (hmin : HasMinimalKernelDegrees A xs)
    (r : ℕ) (f : Fin r → ℕ) (Z : Matrix b (Fin r) K[X]) (hlen : xs.length=r)
    (hsum : xs.sum=∑ j, f j) (hAZ : A*Z=0)
    (hZ : ∀ i j, (Z i j).natDegree≤f j) (x : K)
    (hinj : Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec) :
    HasMinimalKernelDegrees A (List.ofFn f) := by
  classical
  obtain ⟨s,B,e,hB,hlead,hperm⟩ := hmin
  have hrs : s=r := by simpa only [List.length_ofFn,hlen] using hperm.length_eq
  subst s
  let y (j : Fin r) : LinearMap.ker (Matrix.toLin' A) :=
    ⟨fun i => Z i j,by
      change A *ᵥ (fun i => Z i j)=0
      funext i
      exact congrFun (congrFun hAZ i) j⟩
  let W : Matrix (Fin r) (Fin r) K[X] := fun i j => B.equivFun (y j) i
  have hBW : polynomialKernelBasisMatrix A B*W=Z := by
    funext i j
    change (polynomialKernelBasisMatrix A B *ᵥ (B.equivFun (y j))) i=Z i j
    rw [polynomialKernelBasisMatrix_mulVec]
    exact congrArg (fun z : LinearMap.ker (Matrix.toLin' A) => z.val i)
      (B.equivFun.symm_apply_apply (y j))
  let ev := Polynomial.evalRingHom x
  have hWinj : Function.Injective (W.map ev).mulVec := by
    intro u v huv
    apply hinj
    rw [← hBW,Matrix.map_mul]
    simpa only [Matrix.mulVec_mulVec] using
      congrArg ((polynomialKernelBasisMatrix A B).map ev).mulVec huv
  have hdet : (W.map ev).det≠0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hWinj))
  have hσ : ∃ σ : Equiv.Perm (Fin r), ∀ j, (W.map ev) (σ j) j≠0 := by
    by_contra! hz
    apply hdet
    rw [Matrix.det_apply]
    apply Finset.sum_eq_zero
    intro σ _
    obtain ⟨j,hj⟩ := hz σ
    have hzprod : (∏ i, (W.map ev) (σ i) i)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hzprod,smul_zero]
  obtain ⟨σ,hσ⟩ := hσ
  have hle (j : Fin r) : e (σ j)≤f j := by
    have hb := (polynomial_combination_degree_iff
      (polynomialKernelBasisMatrix A B) e (fun i => W i j) (f j) hB hlead).mp (by
        intro k
        change ((polynomialKernelBasisMatrix A B*W) k j).natDegree≤f j
        rw [hBW]
        exact hZ k j) (σ j)
    have hn : W (σ j) j≠0 := by
      intro hz
      exact hσ j (by simp [Matrix.map_apply,hz])
    exact (hb.resolve_left hn).1
  have hs : (∑ j, e (σ j))=∑ j, f j := by
    rw [Equiv.sum_comp σ]
    have hp := hperm.sum_eq
    rw [List.sum_ofFn] at hp
    exact hp.trans hsum
  have heq : ∀ j, e (σ j)=f j :=
    fun j => (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).mp hs j (Finset.mem_univ j)
  have hp : (List.ofFn e).Perm (List.ofFn f) :=
    (σ.ofFn_comp_perm e).symm.trans (List.Perm.of_eq (congrArg List.ofFn (funext heq)))
  exact ⟨r,B,e,hB,hlead,hp⟩

end FD56
