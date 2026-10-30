/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTripleTangentSplice
import FD56.Hilbert.SixOutputTripleTangentPermutation

/-! Normalization of a conditional three-column splice with complementary endpoint frames. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

def sixOutputTripleBaseFrame (R : Type*) [Zero R] [One R] : Matrix (Fin 6) (Fin 3) R :=
  fun i j => if i.val=j.val+3 then 1 else 0

private theorem kernel_smul {F a b : Type*} [Field F] [Fintype b]
    (A : Matrix a b F[X]) (c : F[X]) (hc : c≠0) (d : ℕ) :
    polynomialKernelAtDegree (c • A) d=polynomialKernelAtDegree A d := by
  ext z
  change (c • A)*ᵥ(fun j => (z j).val)=0 ↔ A*ᵥ(fun j => (z j).val)=0
  rw [Matrix.smul_mulVec_assoc]
  constructor
  · intro h
    funext i
    exact (mul_eq_zero.mp (congrFun h i)).resolve_left hc
  · intro h
    rw [h,smul_zero]

private theorem splice_constant {K : Type*} [Field K] (u U : K[X]) :
    (polynomialTailSplice u U 5).coeff 0=monomial 5 (U.coeff 0) := by
  simp [polynomialTailSplice,Finset.sum_range_succ,Polynomial.coeff_monomial]

variable {K F : Type*} [Field K] [Field F]
  [Algebra K[X] F] [IsFractionRing K[X] F]

theorem normalized_six_output_triple_splice_step_of_tail
    (U : Matrix (Fin 6) (Fin 3) K[X])
    (hU : ∀ i j, (U i j).natDegree≤5)
    (hUconst : ∀ i j, (U i j).coeff 0=(if i.val=j.val then 1 else 0 : K))
    (hUtop : ∀ i j, (U i j).coeff 5=sixOutputTripleBaseFrame K i j)
    (hzero : ∀ z : Fin 20 → K[X],
      sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors U)*ᵥz=0 →
      (∀ j, (z j).natDegree≤5) → z=0)
    (G : Matrix (Fin 6) (Fin 3) K[X]) (a : ℕ)
    (hG : ∀ i j, (G i j).coeff 0=sixOutputTripleBaseFrame K i j)
    (hdG : ∀ i j, (G i j).natDegree≤a) :
    ∃ G' : Matrix (Fin 6) (Fin 3) F[X],
      (∀ i j, (G' i j).coeff 0=sixOutputTripleBaseFrame F i j) ∧
      (∀ i j, (G' i j).natDegree≤a+5) ∧
      ∀ d, Module.finrank F (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G')) (d+6)) ≤
        Module.finrank K (polynomialKernelAtDegree
          (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d) := by
  let φ := algebraMap K[X] F
  let c := (φ ((X : K[X])^5))⁻¹
  let P := (sixOutputTripleSpliceFrame G U 5).map (Polynomial.mapRingHom φ)
  let Q := C c • P
  let G' : Matrix (Fin 6) (Fin 3) F[X] := fun i j => Q (sixOutputTripleTailSwap i) j
  have hx : φ ((X : K[X])^5)≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective K[X] F).ne (pow_ne_zero 5 Polynomial.X_ne_zero)
  have hxp : (φ (X : K[X]))^5≠0 := by simpa only [map_pow] using hx
  have hc : c≠0 := inv_ne_zero hx
  have hconst (w W : K[X]) :
      (C c*(polynomialTailSplice w W 5).map φ).coeff 0=
        c*φ (monomial 5 (W.coeff 0)) := by
    rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,splice_constant]
  refine ⟨G',?_,?_,?_⟩
  · intro i j
    change (C c*(polynomialTailSplice (G (sixOutputTripleTailSwap i) j)
      (U (sixOutputTripleTailSwap i) j) 5).map φ).coeff 0=_
    rw [hconst,hUconst]
    fin_cases i <;> fin_cases j <;>
      simp [sixOutputTripleTailSwap,sixOutputTripleBaseFrame,c,← Polynomial.C_mul_X_pow_eq_monomial,hxp] <;>
      change φ (0 : K[X])=0 <;> exact map_zero φ
  · intro i j
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans (polynomialTailSplice_degree _ _ 5 a
        (hdG (sixOutputTripleTailSwap i) j)))
  · intro d
    change Module.finrank F (polynomialKernelAtDegree
      (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors
        (fun i j => Q (sixOutputTripleTailSwap i) j))) (d+6))≤_
    rw [six_output_triple_tail_swap_kernel_finrank]
    have he : sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors Q)=
        (C c)^3 • ((sixOutputTripleSpliceTangent G U 5).map
          (Polynomial.mapRingHom φ)) := by
      rw [sixOutputTripleTangent_frame_smul]
      congr 1
      exact (sixOutputTripleTangent_frame_map (Polynomial.mapRingHom φ) _).symm
    rw [he,kernel_smul _ _ (pow_ne_zero 3 (Polynomial.C_ne_zero.mpr hc))]
    apply six_output_triple_tangent_splice_kernel_finrank_le G U 5 6 d (by omega) hU
    · intro i j
      rw [hUtop,hG]
    · exact hzero

end FD56
