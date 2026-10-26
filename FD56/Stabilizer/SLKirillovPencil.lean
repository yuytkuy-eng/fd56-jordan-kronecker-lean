/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SLTraceChart
import FD56.Stabilizer.GLKirillovPencil

/-! The actual square SL Kirillov pencil in a traceless coordinate chart.
Its radical is compared with the full SL equations, including scalar corrections. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def slKirillovMatrix (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    Matrix (SLChartInput n m i₀) (SLChartInput n m i₀) R :=
  (slChartEmbeddingMatrix i₀).transpose * glKirillovMatrix M P * slChartEmbeddingMatrix i₀

theorem slKirillovMatrix_pairing (M : Matrix n n R) (P : Matrix m n R) (i₀ : n)
    (z w : SLChartInput n m i₀ → R) :
    w ⬝ᵥ (slKirillovMatrix M P i₀ *ᵥ z) =
      (slChartEmbed R R i₀ w) ⬝ᵥ (glKirillovMatrix M P *ᵥ slChartEmbed R R i₀ z) := by
  simp only [slKirillovMatrix, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, slChartEmbeddingMatrix_mulVec]

theorem slKirillovMatrix_alternating (M : Matrix n n R) (P : Matrix m n R) (i₀ : n)
    (z : SLChartInput n m i₀ → R) : z ⬝ᵥ (slKirillovMatrix M P i₀ *ᵥ z) = 0 := by
  rw [slKirillovMatrix_pairing]
  exact glKirillovMatrix_alternating _ _ _

theorem slKirillovMatrix_skew (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    (slKirillovMatrix M P i₀).transpose = -slKirillovMatrix M P i₀ := by
  simp [slKirillovMatrix, Matrix.transpose_mul, glKirillovMatrix_skew, Matrix.mul_assoc]

section Polynomial
variable {K : Type*} [Field K]

theorem slKirillovMatrix_coefficient_skew (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (k : ℕ) :
    Matrix.transpose (fun i j => (slKirillovMatrix M P i₀ i j).coeff k) =
      -(fun i j => (slKirillovMatrix M P i₀ i j).coeff k) := by
  funext i j
  have h := congrArg (fun A => (A i j).coeff k) (slKirillovMatrix_skew M P i₀)
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Polynomial.coeff_neg] using h

theorem slKirillovMatrix_coefficient_alternating (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (k : ℕ) (z : SLChartInput n m i₀ → K) :
    z ⬝ᵥ ((fun i j => (slKirillovMatrix M P i₀ i j).coeff k) *ᵥ z) = 0 := by
  have h := congrArg (fun p : K[X] => p.coeff k)
    (slKirillovMatrix_alternating M P i₀ (fun i => Polynomial.C (z i)))
  simpa only [dotProduct, Matrix.mulVec, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_zero] using h

theorem slKirillovMatrix_degreeBound (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (d : ℕ) (hM : DegreeBound M d) (hP : DegreeBound P d) :
    DegreeBound (slKirillovMatrix M P i₀) d := by
  have hE : DegreeBound (slChartEmbeddingMatrix (R := K[X]) (m := m) i₀) 0 := by
    rw [← slChartEmbeddingMatrix_map (Polynomial.C : K →+* K[X])]
    intro i j
    simp
  have hEt : DegreeBound (slChartEmbeddingMatrix (R := K[X]) (m := m) i₀).transpose 0 :=
    fun i j => hE j i
  exact (by simpa [slKirillovMatrix] using
    degreeBound_mul (degreeBound_mul hEt (glKirillovMatrix_degreeBound M P d hM hP)) hE)

/-- The restricted radical is the full SL radical, not the traceless part of
the GL radical. Every traceless test vector is supplied by the chart. -/
theorem slKirillovMatrix_kernel_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (z : SLChartInput n m i₀ → K[X]) :
    slKirillovMatrix M P i₀ *ᵥ z = 0 ↔
      slEquationMatrix M P i₀ *ᵥ slChartEmbed K[X] K[X] i₀ z = 0 := by
  rw [slEquationMatrix_kernel_iff]
  constructor
  · intro hz
    refine ⟨slChartEmbed_trace _ _ i₀ z, ?_⟩
    intro Y W hY
    let v := (matrixPairEquiv K[X] K[X] n m).symm (Y,W)
    have ht : slInputTrace K[X] K[X] v = 0 := hY
    have he := slChartEmbed_retract K[X] K[X] i₀ v ht
    have h := slKirillovMatrix_pairing M P i₀ z (slChartRetract K[X] K[X] i₀ v)
    rw [hz, dotProduct_zero, he, glKirillovMatrix_pairing] at h
    exact h.symm
  · intro hz
    funext i
    have h := hz.2
      (matrixPairEquiv K[X] K[X] n m (slChartEmbed K[X] K[X] i₀ (Pi.single i 1))).1
      (matrixPairEquiv K[X] K[X] n m (slChartEmbed K[X] K[X] i₀ (Pi.single i 1))).2
      (slChartEmbed_trace _ _ i₀ _)
    have hp := slKirillovMatrix_pairing M P i₀ z (Pi.single i 1)
    rw [glKirillovMatrix_pairing] at hp
    simpa only [single_dotProduct, one_mul] using hp.trans h

omit [Fintype m] in
theorem slChartEmbed_bounded_val (i₀ : n) (d : ℕ)
    (v : SLChartInput n m i₀ → BoundedPoly K d) :
    (fun i => (slChartEmbed K (BoundedPoly K d) i₀ v i).val) =
      slChartEmbed K[X] K[X] i₀ (fun i => (v i).val) :=
  slChartEmbed_map (R := K) (S := K[X])
    (Polynomial.degreeLT K (d+1)).subtype.toAddMonoidHom i₀ v

theorem slEquationMatrix_kernel_trace (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (v : SLInput n m → K[X]) (hv : slEquationMatrix M P i₀ *ᵥ v = 0) :
    slInputTrace K[X] K[X] v = 0 :=
  ((slEquationMatrix_kernel_iff M P i₀ v).mp hv).1

theorem slEquationMatrix_bounded_kernel_trace (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (d : ℕ) (v : polynomialKernelAtDegree (slEquationMatrix M P i₀) d) :
    slInputTrace K (BoundedPoly K d) v.val = 0 := by
  apply Subtype.ext
  have h := slEquationMatrix_kernel_trace M P i₀ (fun i => (v.val i).val) v.property
  simpa only [slInputTrace, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
    Submodule.coe_zero] using h

/-- The constant chart preserves every bounded polynomial kernel exactly. -/
def slKirillovMatrix_boundedKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (d : ℕ) :
    polynomialKernelAtDegree (slKirillovMatrix M P i₀) d ≃ₗ[K]
      polynomialKernelAtDegree (slEquationMatrix M P i₀) d where
  toFun z := ⟨slChartEmbed K (BoundedPoly K d) i₀ z.val, by
    change slEquationMatrix M P i₀ *ᵥ
      (fun i => (slChartEmbed K (BoundedPoly K d) i₀ z.val i).val) = 0
    rw [slChartEmbed_bounded_val]
    exact (slKirillovMatrix_kernel_iff M P i₀ _).mp z.property⟩
  invFun v := ⟨slChartRetract K (BoundedPoly K d) i₀ v.val, by
    change slKirillovMatrix M P i₀ *ᵥ
      slChartRetract K[X] K[X] i₀ (fun i => (v.val i).val) = 0
    apply (slKirillovMatrix_kernel_iff M P i₀ _).mpr
    rw [slChartEmbed_retract K[X] K[X] i₀ _
      (slEquationMatrix_kernel_trace M P i₀ _ v.property)]
    exact v.property⟩
  left_inv z := by
    apply Subtype.ext
    exact slChartRetract_embed _ _ i₀ z.val
  right_inv v := by
    apply Subtype.ext
    exact slChartEmbed_retract _ _ i₀ v.val (slEquationMatrix_bounded_kernel_trace M P i₀ d v)
  map_add' z w := by
    apply Subtype.ext
    exact map_add (slChartEmbed K (BoundedPoly K d) i₀) z.val w.val
  map_smul' c z := by
    apply Subtype.ext
    exact map_smul (slChartEmbed K (BoundedPoly K d) i₀) c z.val

theorem slKirillovMatrix_polynomialKernelAtDegree_finrank (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (i₀ : n) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (slKirillovMatrix M P i₀) d) =
      Module.finrank K (polynomialKernelAtDegree (slEquationMatrix M P i₀) d) :=
  (slKirillovMatrix_boundedKernelEquiv M P i₀ d).finrank_eq

theorem slKirillovMatrix_hasMinimalKernelDegrees_iff (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (i₀ : n) (degrees : List ℕ) :
    HasMinimalKernelDegrees (slKirillovMatrix M P i₀) degrees ↔
      HasMinimalKernelDegrees (slEquationMatrix M P i₀) degrees := by
  rw [hasMinimalKernelDegrees_iff_hilbert, hasMinimalKernelDegrees_iff_hilbert]
  apply forall_congr'
  intro d
  rw [slKirillovMatrix_polynomialKernelAtDegree_finrank M P i₀ d]

end Polynomial
end FD56
