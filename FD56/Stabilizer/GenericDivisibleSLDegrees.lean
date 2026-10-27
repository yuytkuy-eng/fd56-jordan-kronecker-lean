/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SeparableObservabilitySLDegrees
import FD56.Stabilizer.GenericDivisibleSLNullity

/-! The unique minimal index of every positive divisible generic SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} {m : Type} [Field K] [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
theorem divisible_observability_weight_sum (q : ℕ) :
    (∑ i : Fin q × m, (i.1.val+1))=Fintype.card m*q*(q+1)/2 := by
  have hsum : 2*(∑ i : Fin q, (i.val+1))=q*(q+1) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc,Fin.val_last]
      nlinarith [ih]
  have hp : (∑ i : Fin q × m, (i.1.val+1))=
      Fintype.card m*(∑ i : Fin q, (i.val+1)) := by
    simp [Fintype.sum_prod_type,← Finset.mul_sum]
  have ht : 2*(∑ i : Fin q × m, (i.1.val+1))=Fintype.card m*q*(q+1) := by
    rw [hp]
    nlinarith [congrArg (fun a => Fintype.card m*a) hsum]
  omega

theorem generic_divisible_gl_equation_injective (q : ℕ) :
    Function.Injective (glEquationMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m)).mulVec := by
  let M := genericAffineSquare K (Fin q × m) m
  let P := genericAffineRows K (Fin q × m) m
  intro u v huv
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero (generic_divisible_gl_kirillov_det_ne_zero K m q)
  apply (glKirillovMatrix_kernel_iff M P (u-v)).mpr
  rw [Matrix.mulVec_sub,huv,sub_self]

theorem generic_divisible_sl_minimal_degrees (q : ℕ) (i₀ : Fin (q+1) × m) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) i₀)
      [Fintype.card m*(q+1)*(q+2)/2-1] := by
  let M := genericAffineSquare K (Fin (q+1) × m) m
  let P := genericAffineRows K (Fin (q+1) × m) m
  have hp : 0<(∑ i : Fin (q+1) × m, (i.1.val+1)) := by
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₀,Finset.mem_univ _,by omega⟩
  have he : (∑ i : Fin (q+1) × m, (i.1.val+1))=
      (Fintype.card m*(q+1)*(q+2)/2-1)+1 := by
    rw [divisible_observability_weight_sum] at hp ⊢
    norm_num only [Nat.add_assoc] at hp ⊢
    omega
  have hLower : ∀ k : Fin (q+1) × m, ∀ s, s<k.1.val → ∀ a : m,
      ∃ l : Fin (q+1) × m, l.1.val=s ∧ l.2=a := by
    intro k s hs a
    exact ⟨(⟨s,lt_trans hs k.1.isLt⟩,a),rfl,rfl⟩
  obtain ⟨hd,hs⟩ := generic_divisible_observability_separable K m (q+1)
  apply sl_minimal_degrees_of_separable_observability
    (F := GenericPencilField K (Fin (q+1) × m) m) M P i₀
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (fun i => i.1.val) Prod.snd _ he hLower hs
  · exact hd.trans he
  · exact generic_divisible_gl_equation_injective (q+1)
  · exact generic_divisible_sl_nullity q i₀

theorem generic_divisible_sl_kirillov_minimal_degrees (q : ℕ) (i₀ : Fin (q+1) × m) :
    HasMinimalKernelDegrees (slKirillovMatrix
      (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) i₀)
      [Fintype.card m*(q+1)*(q+2)/2-1] :=
  (slKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _ _).mpr
    (generic_divisible_sl_minimal_degrees q i₀)

theorem generic_divisible_sl_hilbert (q : ℕ) (i₀ : Fin (q+1) × m) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) d=
      d+1-(Fintype.card m*(q+1)*(q+2)/2-1) := by
  rw [slHilbert_eq_matrix_kernel _ _ i₀,
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp (generic_divisible_sl_minimal_degrees q i₀)]
  simp

end FD56
