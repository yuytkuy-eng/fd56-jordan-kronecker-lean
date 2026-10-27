/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleSLDegrees
import FD56.LinearAlgebra.WeightedDeterminantDegree

/-! Separable full-degree observability gives the SL minimal index for concrete affine pairs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]

theorem slEquationMatrix_fraction_nullity_of_regular_gl
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n)
    (hd : (glKirillovMatrix M P).det≠0) :
    Module.finrank (FractionRing K[X]) (LinearMap.ker (Matrix.toLin'
      ((slEquationMatrix M P i₀).map (algebraMap K[X] (FractionRing K[X])))))=1 := by
  let φ := algebraMap K[X] (FractionRing K[X])
  have hdet : (glKirillovMatrix (M.map φ) (P.map φ)).det≠0 := by
    intro hz
    have he := φ.map_det (glKirillovMatrix M P)
    change φ (glKirillovMatrix M P).det=((glKirillovMatrix M P).map φ).det at he
    rw [glKirillovMatrix_map,hz] at he
    exact hd ((IsFractionRing.injective _ _) (he.trans (map_zero φ).symm))
  rw [slEquationMatrix_map]
  exact slEquationMatrix_nullity_of_gl_det_ne_zero (M.map φ) (P.map φ) i₀ hdet

variable {m : Type} [Fintype m] [DecidableEq m]

theorem divisible_observability_degree_of_gl_leading (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) K[X])
    (P : Matrix m (Fin (q+1) × m) K[X])
    (hm : 0<Fintype.card m) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hd : (observabilityMatrix M P (q+1)).det≠0)
    (hlead : Matrix.det (fun i j => (glKirillovMatrix M P i j).coeff 1)≠0) :
    (observabilityMatrix M P (q+1)).det.natDegree=∑ i : Fin (q+1) × m, (i.1.val+1) := by
  have hdet := glKirillovMatrix_det_observability_ne_zero q M P hd
  have hdegree := polynomial_det_natDegree_eq_row_sum (glKirillovMatrix M P) (fun _ => 1)
    (glKirillovMatrix_degreeBound M P 1 hM hP) hlead
  rw [hdet,Polynomial.natDegree_pow] at hdegree
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hdegree
  have hgeneric := generic_divisible_gl_kirillov_det_degree K m (q+1)
  rw [generic_divisible_gl_kirillov_determinant,Polynomial.natDegree_pow,
    (generic_divisible_observability_separable K m (q+1)).1] at hgeneric
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0<2*Fintype.card m) (hdegree.trans hgeneric.symm)

theorem divisible_sl_minimal_degrees_of_observability (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) K[X])
    (P : Matrix m (Fin (q+1) × m) K[X]) (i₀ : Fin (q+1) × m)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hs : (observabilityMatrix M P (q+1)).det.Separable)
    (hlead : Matrix.det (fun i j => (glKirillovMatrix M P i j).coeff 1)≠0) :
    HasMinimalKernelDegrees (slEquationMatrix M P i₀) [Fintype.card m*(q+1)*(q+2)/2-1] := by
  letI : Nonempty m := ⟨i₀.2⟩
  have hm : 0<Fintype.card m := Fintype.card_pos
  have hdet : (glKirillovMatrix M P).det≠0 := by
    rw [glKirillovMatrix_det_observability_ne_zero q M P hs.ne_zero]
    exact pow_ne_zero _ hs.ne_zero
  have hinj : Function.Injective (glEquationMatrix M P).mulVec := by
    intro u v huv
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    apply (glKirillovMatrix_kernel_iff M P (u-v)).mpr
    rw [Matrix.mulVec_sub,huv,sub_self]
  have hp : 0<(∑ i : Fin (q+1) × m, (i.1.val+1)) :=
    Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₀,Finset.mem_univ _,by omega⟩
  have he : (∑ i : Fin (q+1) × m, (i.1.val+1))=
      (Fintype.card m*(q+1)*(q+2)/2-1)+1 := by
    rw [divisible_observability_weight_sum] at hp ⊢
    norm_num only [Nat.add_assoc] at hp ⊢
    omega
  apply sl_minimal_degrees_of_separable_observability (F := FractionRing K[X]) M P i₀ hM hP
    (fun i => i.1.val) Prod.snd _ he
  · intro k s hs a
    exact ⟨(⟨s,lt_trans hs k.1.isLt⟩,a),rfl,rfl⟩
  · exact hs
  · exact (divisible_observability_degree_of_gl_leading q M P hm hM hP hs.ne_zero hlead).trans he
  · exact hinj
  · exact slEquationMatrix_fraction_nullity_of_regular_gl M P i₀ hdet

end FD56
