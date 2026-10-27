/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.DivisibleObservabilityCertificate

/-! A single scalar nonvanishing condition preserves polynomial observability
certificates under arbitrary coefficient specialization. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {R K : Type*} {m : Type} [CommRing R] [Field K]
  [Fintype m] [DecidableEq m]

theorem divisible_observability_certificate_specialization (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) R[X])
    (P : Matrix m (Fin (q+1) × m) R[X])
    (W : Matrix (Fin (q+1) × m) (Fin q × m) R[X])
    (V : Matrix (Fin (q+1) × m) (Fin (q+2) × m) R[X])
    (A B : R[X]) (dW dV dS : R)
    (hW : observabilityMatrix M P q*W=C dW•1)
    (hV : V*observabilityMatrix M P (q+2)=C dV•1)
    (hS : A*(observabilityMatrix M P (q+1)).det+
      B*(observabilityMatrix M P (q+1)).det.derivative=C dS)
    (ψ : R →+* K) (hd : ψ (dW*dV*dS)≠0) :
    let M' := M.map (Polynomial.mapRingHom ψ)
    let P' := P.map (Polynomial.mapRingHom ψ)
    (observabilityMatrix M' P' (q+1)).det.Separable ∧
      (∃ W' : Matrix (Fin (q+1) × m) (Fin q × m) K[X],
        observabilityMatrix M' P' q*W'=1) ∧
      (∃ V' : Matrix (Fin (q+1) × m) (Fin (q+2) × m) K[X],
        V'*observabilityMatrix M' P' (q+2)=1) := by
  let φ := Polynomial.mapRingHom ψ
  let M' := M.map φ
  let P' := P.map φ
  have hdW : ψ dW≠0 := by
    intro hz
    apply hd
    simp [map_mul,hz]
  have hdV : ψ dV≠0 := by
    intro hz
    apply hd
    simp [map_mul,hz]
  have hdS : ψ dS≠0 := by
    intro hz
    apply hd
    simp [map_mul,hz]
  have hscalar {a : Type} [DecidableEq a] (d : R) :
      (C d•(1 : Matrix a a R[X])).map φ=C (ψ d)•1 := by
    funext i j
    by_cases h : i=j <;>
      simp [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,φ,h]
  have hWmap : observabilityMatrix M' P' q*W.map φ=C (ψ dW)•1 := by
    have h := congrArg (fun Z => Z.map φ) hW
    dsimp only at h
    rw [Matrix.map_mul,observabilityMatrix_map,hscalar] at h
    exact h
  have hVmap : V.map φ*observabilityMatrix M' P' (q+2)=C (ψ dV)•1 := by
    have h := congrArg (fun Z => Z.map φ) hV
    dsimp only at h
    rw [Matrix.map_mul,observabilityMatrix_map,hscalar] at h
    exact h
  have hdet : (observabilityMatrix M' P' (q+1)).det=
      ((observabilityMatrix M P (q+1)).det).map ψ := by
    rw [← observabilityMatrix_map]
    exact (φ.map_det _).symm
  refine ⟨?_,?_,?_⟩
  · apply polynomial_separable_of_bezout_constant _ (A.map ψ) (B.map ψ) (ψ dS) hdS
    rw [hdet,Polynomial.derivative_map,← Polynomial.map_mul,
      ← Polynomial.map_mul,← Polynomial.map_add,hS,Polynomial.map_C]
  · refine ⟨C (ψ dW)⁻¹•W.map φ,?_⟩
    rw [Matrix.mul_smul,hWmap,smul_smul,← map_mul,inv_mul_cancel₀ hdW,map_one,one_smul]
  · refine ⟨C (ψ dV)⁻¹•V.map φ,?_⟩
    rw [Matrix.smul_mul,hVmap,smul_smul,← map_mul,inv_mul_cancel₀ hdV,map_one,one_smul]

end FD56
