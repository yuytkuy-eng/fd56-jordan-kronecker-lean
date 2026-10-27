/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ScalarDivisibility
import FD56.Hilbert.SLScalarCrossVanishing

/-! Scalar-image divisibility rules out low-degree full SL radical vectors. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem slHilbert_zero_of_scalar_divisibility
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n) (d : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (Z : SLInput n m → K[X]) (p q : K[X])
    (ℓ : (SLInput n m → K[X]) →ₗ[K[X]] K[X])
    (hZ : glEquationMatrix M P *ᵥ Z = p • glScalarVector K[X] n m)
    (hℓ : ℓ Z = q) (hcp : IsCoprime p q)
    (hinj : Function.Injective (glEquationMatrix M P).mulVec)
    (hdegree : d+1 < p.natDegree) : slHilbert M P d = 0 := by
  letI : Nonempty n := ⟨i₀⟩
  unfold slHilbert
  apply Submodule.finrank_eq_zero.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  obtain ⟨_,hPX,f,hf⟩ := (slRadical_iff_equations M P (entries z.1) (entries z.2)).mp hz
  let v := (matrixPairEquiv K[X] K[X] n m).symm (entries z.1,entries z.2)
  have hres : stabilizerResidual M P (entries z.1,entries z.2)=f • 1 := by
    change M*entries z.1-entries z.1*M-entries z.2*P=f • 1
    rw [hf,add_sub_cancel_left]
  have hv : glEquationMatrix M P *ᵥ v=f • glScalarVector K[X] n m := by
    apply (glEquationMatrix_scalar_iff M P v f).mpr
    simpa only [v,LinearEquiv.apply_symm_apply] using And.intro hPX hres
  have hdegf : f.natDegree ≤ d+1 := by
    have he : stabilizerResidual M P (entries z.1,entries z.2) i₀ i₀=f := by simp [hres]
    rw [← he]
    exact bounded_stabilizer_residual_degree M P hM hP d z i₀ i₀
  have hzv : v=0 := polynomial_scalar_solution_zero_of_degree
    (Matrix.toLin' (glEquationMatrix M P)) hinj ℓ (glScalarVector K[X] n m)
    Z p q hZ hℓ hcp v f hv (hdegf.trans_lt hdegree)
  apply Prod.ext
  · funext i j
    apply Subtype.ext
    exact congrFun hzv (.inl (i,j))
  · funext i j
    apply Subtype.ext
    exact congrFun hzv (.inr (i,j))

end FD56
