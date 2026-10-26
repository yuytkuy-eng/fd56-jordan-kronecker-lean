/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A finite determinant certificate for separability of a monic polynomial. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]

def derivativeRemainderMatrix (f : R[X]) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => ((f.derivative * X ^ j.val) %ₘ f).coeff i.val

theorem derivativeRemainderMatrix_map (f : R[X]) (hf : f.Monic)
    (N : ℕ) (φ : R →+* S) :
    (derivativeRemainderMatrix f N).map φ = derivativeRemainderMatrix (f.map φ) N := by
  ext i j
  simp only [derivativeRemainderMatrix,Matrix.map_apply,← coeff_map,
    map_modByMonic φ hf,Polynomial.map_mul,derivative_map,Polynomial.map_pow,map_X]

theorem adjoinRoot_mk_isUnit_iff (f g : R[X]) :
    IsUnit (AdjoinRoot.mk f g) ↔ IsCoprime f g := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨b,rfl⟩ := AdjoinRoot.mk_surjective x
    have he : AdjoinRoot.mk f (g*b-1) = 0 := by simpa using sub_eq_zero.mpr hx
    obtain ⟨a,ha⟩ := AdjoinRoot.mk_eq_zero.mp he
    refine ⟨-a,b,?_⟩
    linear_combination ha
  · rintro ⟨a,b,h⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨AdjoinRoot.mk f b,?_⟩
    have hh := congrArg (AdjoinRoot.mk f) h
    simpa [mul_comm] using hh

theorem leftMulMatrix_isUnit_iff {A ι : Type*} [CommRing A] [Algebra R A]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R A) (x : A) :
    IsUnit (Algebra.leftMulMatrix b x) ↔ IsUnit x := by
  constructor
  · intro h
    obtain ⟨v,hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr h) (b.equivFun 1)
    let y := b.equivFun.symm v
    apply isUnit_iff_exists_inv.mpr
    refine ⟨y, b.equivFun.injective ?_⟩
    have he := Algebra.leftMulMatrix_mulVec_repr b x y
    change (Algebra.leftMulMatrix b x).mulVec (b.equivFun y) = b.equivFun (x*y) at he
    rw [show b.equivFun y = v by exact b.equivFun.apply_symm_apply v] at he
    exact he.symm.trans hv
  · exact fun h => h.map (Algebra.leftMulMatrix b)

theorem derivativeRemainderMatrix_eq_leftMul (f : R[X]) (hf : f.Monic) :
    derivativeRemainderMatrix f f.natDegree =
      Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis (AdjoinRoot.mk f f.derivative) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,(AdjoinRoot.powerBasis' hf).basis_eq_pow]
  change _ = (AdjoinRoot.powerBasisAux' hf).repr
    (AdjoinRoot.mk f f.derivative * (AdjoinRoot.root f)^j.val) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simp only [AdjoinRoot.root,← map_pow,← map_mul,AdjoinRoot.modByMonicHom_mk]
  rfl

theorem derivativeRemainderMatrix_isUnit_iff (f : R[X]) (hf : f.Monic) :
    IsUnit (derivativeRemainderMatrix f f.natDegree).det ↔ f.Separable := by
  rw [← Matrix.isUnit_iff_isUnit_det,derivativeRemainderMatrix_eq_leftMul f hf,
    leftMulMatrix_isUnit_iff,adjoinRoot_mk_isUnit_iff,separable_def]

theorem monic_separable_of_specialization {F L : Type*} [Field F] [Field L]
    (f : R[X]) (hf : f.Monic) (φ : R →+* L) (ψ : R →+* F)
    (hψ : Function.Injective ψ) (hs : (f.map φ).Separable) : (f.map ψ).Separable := by
  have hd : (derivativeRemainderMatrix f f.natDegree).det ≠ 0 := by
    intro hz
    have hφ : φ (derivativeRemainderMatrix f f.natDegree).det =
        ((derivativeRemainderMatrix f f.natDegree).map φ).det := φ.map_det _
    have hu := (derivativeRemainderMatrix_isUnit_iff (f.map φ) (hf.map φ)).mpr hs
    rw [hf.natDegree_map φ,← derivativeRemainderMatrix_map f hf f.natDegree φ,
      ← hφ] at hu
    exact hu.ne_zero (by rw [hz,map_zero])
  have hψdet : ψ (derivativeRemainderMatrix f f.natDegree).det =
      ((derivativeRemainderMatrix f f.natDegree).map ψ).det := ψ.map_det _
  apply (derivativeRemainderMatrix_isUnit_iff (f.map ψ) (hf.map ψ)).mp
  rw [hf.natDegree_map ψ,← derivativeRemainderMatrix_map f hf f.natDegree ψ,
    ← hψdet]
  exact isUnit_iff_ne_zero.mpr (fun hz => hd (hψ (hz.trans (map_zero ψ).symm)))

end FD56
