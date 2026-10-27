/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleRootProfile

/-! Finite polynomial identities certify the observability profile at every
root, without requiring a generic coefficient-field embedding. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L : Type*} {m : Type} [Field K] [Field L]
  [Fintype m] [DecidableEq m]

theorem polynomial_separable_of_bezout_constant (f A B : K[X]) (d : K)
    (hd : d≠0) (h : A*f+B*f.derivative=C d) : f.Separable := by
  rw [Polynomial.separable_def]
  refine ⟨C d⁻¹*A,C d⁻¹*B,?_⟩
  calc
    _ = C d⁻¹*(A*f+B*f.derivative) := by ring
    _ = 1 := by rw [h,← map_mul,inv_mul_cancel₀ hd,map_one]

theorem divisible_observability_certificate_root_profile (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) K[X])
    (P : Matrix m (Fin (q+1) × m) K[X])
    (R : Matrix (Fin (q+1) × m) (Fin q × m) K[X])
    (V : Matrix (Fin (q+1) × m) (Fin (q+2) × m) K[X])
    (A B : K[X]) (dR dV dS : K)
    (hR : observabilityMatrix M P q*R=C dR•1)
    (hV : V*observabilityMatrix M P (q+2)=C dV•1)
    (hS : A*(observabilityMatrix M P (q+1)).det+
      B*(observabilityMatrix M P (q+1)).det.derivative=C dS)
    (hdR : dR≠0) (hdV : dV≠0) (hdS : dS≠0)
    (φ : K →+* L) (x : L)
    (hx : (observabilityMatrix M P (q+1)).det.eval₂ φ x=0) :
    let M' := M.map (Polynomial.eval₂RingHom φ x)
    let P' := P.map (Polynomial.eval₂RingHom φ x)
    Module.finrank L (unobservableSpace M' P' q)=Fintype.card m ∧
      Module.finrank L (unobservableSpace M' P' (q+1))=1 ∧
      Module.finrank L (unobservableSpace M' P' (q+2))=0 := by
  let ev := Polynomial.eval₂RingHom φ x
  let M' := M.map ev
  let P' := P.map ev
  have hdR' : φ dR≠0 := fun hz => hdR (φ.injective (hz.trans (map_zero φ).symm))
  have hdV' : φ dV≠0 := fun hz => hdV (φ.injective (hz.trans (map_zero φ).symm))
  have hscalar {a : Type} [DecidableEq a] (d : K) :
      (C d•(1 : Matrix a a K[X])).map ev=φ d•1 := by
    funext i j
    by_cases h : i=j <;>
      simp [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,ev,h]
  have hRmap : observabilityMatrix M' P' q*R.map ev=φ dR•1 := by
    have h := congrArg (fun Z => Z.map ev) hR
    dsimp only at h
    rw [Matrix.map_mul,observabilityMatrix_map,hscalar] at h
    exact h
  have hVmap : V.map ev*observabilityMatrix M' P' (q+2)=φ dV•1 := by
    have h := congrArg (fun Z => Z.map ev) hV
    dsimp only at h
    rw [Matrix.map_mul,observabilityMatrix_map,hscalar] at h
    exact h
  have hright : observabilityMatrix M' P' q*((φ dR)⁻¹•R.map ev)=1 := by
    rw [Matrix.mul_smul,hRmap,smul_smul,inv_mul_cancel₀ hdR',one_smul]
  have hleft : ((φ dV)⁻¹•V.map ev)*observabilityMatrix M' P' (q+2)=1 := by
    rw [Matrix.smul_mul,hVmap,smul_smul,inv_mul_cancel₀ hdV',one_smul]
  have hsurj : Function.Surjective (observabilityMatrix M' P' q).mulVec := by
    intro v
    exact ⟨((φ dR)⁻¹•R.map ev)*ᵥv,by rw [Matrix.mulVec_mulVec,hright,Matrix.one_mulVec]⟩
  have hinj : Function.Injective (observabilityMatrix M' P' (q+2)).mulVec := by
    intro v w h
    have hh := congrArg (fun z => ((φ dV)⁻¹•V.map ev)*ᵥz) h
    simpa only [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec] using hh
  refine ⟨?_,?_,?_⟩
  · have hr := surjective_matrix_kernel_finrank _ hsurj
    rw [observabilityMatrix_ker] at hr
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.add_mul,one_mul,
      Nat.add_sub_cancel_left] using hr
  · have hs := polynomial_separable_of_bezout_constant _ A B dS hdS hS
    have he := polynomial_matrix_separable_root_kernel_finrank
      (observabilityMatrix M P (q+1)) φ x hs hx
    rw [observabilityMatrix_map,observabilityMatrix_ker] at he
    exact he
  · rw [← observabilityMatrix_ker,LinearMap.ker_eq_bot.mpr hinj,finrank_bot]

theorem divisible_observability_inverse_root_profile (q : ℕ)
    (M : Matrix (Fin (q+1) × m) (Fin (q+1) × m) K[X])
    (P : Matrix m (Fin (q+1) × m) K[X])
    (R : Matrix (Fin (q+1) × m) (Fin q × m) K[X])
    (V : Matrix (Fin (q+1) × m) (Fin (q+2) × m) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (hV : V*observabilityMatrix M P (q+2)=1)
    (hs : (observabilityMatrix M P (q+1)).det.Separable)
    (φ : K →+* L) (x : L)
    (hx : (observabilityMatrix M P (q+1)).det.eval₂ φ x=0) :
    let M' := M.map (Polynomial.eval₂RingHom φ x)
    let P' := P.map (Polynomial.eval₂RingHom φ x)
    Module.finrank L (unobservableSpace M' P' q)=Fintype.card m ∧
      Module.finrank L (unobservableSpace M' P' (q+1))=1 ∧
      Module.finrank L (unobservableSpace M' P' (q+2))=0 := by
  obtain ⟨A,B,hAB⟩ := (Polynomial.separable_def _).mp hs
  exact divisible_observability_certificate_root_profile q M P R V A B 1 1 1
    (by simpa using hR) (by simpa using hV) (by simpa using hAB)
    one_ne_zero one_ne_zero one_ne_zero φ x hx

end FD56
