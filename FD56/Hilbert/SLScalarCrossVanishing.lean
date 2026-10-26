/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ScalarCrossVanishing
import FD56.Hilbert.GLMatrix
import FD56.Hilbert.MiddleSLHilbert

/-! Scalar lifts and a GL degree gap force vanishing in the full SL radical. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def glScalarVector (R n m : Type*) [CommRing R] [DecidableEq n] :
    ((m × n) ⊕ (n × n)) → R :=
  Sum.elim (fun _ => 0) (fun ij => (1 : Matrix n n R) ij.1 ij.2)

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem glEquationMatrix_scalar_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (v : SLInput n m → K[X]) (c : K[X]) :
    glEquationMatrix M P *ᵥ v = c • glScalarVector K[X] n m ↔
      P * (matrixPairEquiv K[X] K[X] n m v).1 = 0 ∧
      stabilizerResidual M P (matrixPairEquiv K[X] K[X] n m v) = c • 1 := by
  have he : glEquationMatrix M P *ᵥ v = Sum.elim
      (fun ij => (P * (matrixPairEquiv K[X] K[X] n m v).1) ij.1 ij.2)
      (fun ij => stabilizerResidual M P (matrixPairEquiv K[X] K[X] n m v) ij.1 ij.2) := by
    change Matrix.toLin' (LinearMap.toMatrix' (glEquationLinearMap M P)) v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  rw [he]
  constructor
  · intro h
    constructor
    · funext i j
      simpa [glScalarVector] using congrFun h (.inl (i,j))
    · funext i j
      simpa [glScalarVector] using congrFun h (.inr (i,j))
  · rintro ⟨hp,hr⟩
    funext i
    rcases i with ij | ij <;> simp [hp,hr,glScalarVector]

theorem slHilbert_zero_of_scalar_lifts
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n) (d : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (Z₀ Z₁ : SLInput n m → K[X]) (p₀ p₁ : K[X])
    (h₀ : glEquationMatrix M P *ᵥ Z₀ = p₀ • glScalarVector K[X] n m)
    (h₁ : glEquationMatrix M P *ᵥ Z₁ = p₁ • glScalarVector K[X] n m)
    (hZ₀ : ∀ j, (Z₀ j).natDegree ≤ d+1) (hZ₁ : ∀ j, (Z₁ j).natDegree ≤ d+1)
    (hp₀ : p₀.natDegree ≤ d+2) (hp₁ : p₁.natDegree ≤ d+2)
    (hcross : p₁ • Z₀-p₀ • Z₁ ≠ 0)
    (hker : Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) (2*d+2))=0) :
    slHilbert M P d=0 := by
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
  have hzv : v=0 := polynomial_scalar_lifts_low_degree_zero
    (glEquationMatrix M P) (glScalarVector K[X] n m) d Z₀ Z₁ p₀ p₁ h₀ h₁
    hZ₀ hZ₁ hp₀ hp₁ hcross hker v f hv
    (by intro j; rcases j with ij | ij
        · exact boundedPoly_degree d (z.1 ij.1 ij.2)
        · exact boundedPoly_degree d (z.2 ij.1 ij.2)) hdegf
  apply Prod.ext
  · funext i j
    apply Subtype.ext
    exact congrFun hzv (.inl (i,j))
  · funext i j
    apply Subtype.ext
    exact congrFun hzv (.inr (i,j))

end FD56
