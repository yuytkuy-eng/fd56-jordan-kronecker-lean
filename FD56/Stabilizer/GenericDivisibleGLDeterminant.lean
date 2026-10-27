/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLObservabilityDeterminant
import FD56.Stabilizer.GenericDivisibleObservability

/-! Exact determinant, degree, and root orders for every generic divisible GL pencil.
These results do not determine the individual regular Jordan blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable (K m : Type*) [Field K] [Fintype m] [DecidableEq m]

theorem generic_divisible_gl_kirillov_determinant (q : ℕ) :
    (glKirillovMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m)).det=
    (observabilityMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) q).det^(2*Fintype.card m) := by
  cases q with
  | zero => simp [Matrix.det_isEmpty]
  | succ q =>
    exact glKirillovMatrix_det_observability_ne_zero q _ _
      (generic_divisible_observability_nonzero K m (q+1))

theorem generic_divisible_gl_kirillov_det_ne_zero (q : ℕ) :
    (glKirillovMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m)).det≠0 := by
  rw [generic_divisible_gl_kirillov_determinant]
  exact pow_ne_zero _ (generic_divisible_observability_nonzero K m q)

private theorem twice_sum_fin_succ (q : ℕ) :
    2*(∑ i : Fin q, (i.val+1))=q*(q+1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    nlinarith [ih]

theorem generic_divisible_gl_kirillov_det_degree (q : ℕ) :
    (glKirillovMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m)).det.natDegree=
      Fintype.card (SLInput (Fin q × m) m) := by
  rw [generic_divisible_gl_kirillov_determinant,Polynomial.natDegree_pow,
    (generic_divisible_observability_separable K m q).1]
  have hsum : (∑ i : Fin q × m, (i.1.val+1))=
      Fintype.card m*(∑ i : Fin q, (i.val+1)) := by
    simp [Fintype.sum_prod_type,← Finset.mul_sum]
  rw [hsum]
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  calc
    _ = Fintype.card m*Fintype.card m*(2*(∑ i : Fin q, (i.val+1))) := by ring
    _ = _ := by rw [twice_sum_fin_succ]; ring

theorem generic_divisible_gl_leading_det_ne_zero (q : ℕ) :
    Matrix.det (fun i j => (glKirillovMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) i j).coeff 1)≠0 := by
  let H := glKirillovMatrix (genericAffineSquare K (Fin q × m) m)
    (genericAffineRows K (Fin q × m) m)
  have hd : H.det.natDegree=Fintype.card (SLInput (Fin q × m) m) :=
    generic_divisible_gl_kirillov_det_degree K m q
  have hc := polynomial_det_coefficient_row_sum H (fun _ => 1)
    (glKirillovMatrix_degreeBound _ _ 1 (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hc
  rw [← hc,← hd]
  exact Polynomial.leadingCoeff_ne_zero.mpr (generic_divisible_gl_kirillov_det_ne_zero K m q)

private theorem rootMultiplicity_power {F : Type*} [Field F] (p : F[X]) (hp : p≠0)
    (a : F) (k : ℕ) : rootMultiplicity a (p^k)=k*rootMultiplicity a p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hp) hp),ih]
    exact (Nat.succ_mul k _).symm

theorem generic_divisible_gl_det_rootMultiplicity (q : ℕ) {L : Type*} [Field L]
    (phi : AffineCoefficientField K (MatrixParameters (Fin q × m) m) →+* L) (a : L)
    (ha : ((observabilityMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) q).det.map phi).IsRoot a) :
    rootMultiplicity a ((glKirillovMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m)).det.map phi)=2*Fintype.card m := by
  have hs : ((observabilityMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) q).det.map phi).Separable :=
    (generic_divisible_observability_separable K m q).2.map
  have hm : rootMultiplicity a ((observabilityMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) q).det.map phi)=1 := by
    have hle := rootMultiplicity_le_one_of_separable hs a
    have hpos := (Polynomial.rootMultiplicity_pos hs.ne_zero).mpr ha
    omega
  rw [generic_divisible_gl_kirillov_determinant,Polynomial.map_pow,
    rootMultiplicity_power _ hs.ne_zero,hm,mul_one]

end FD56
