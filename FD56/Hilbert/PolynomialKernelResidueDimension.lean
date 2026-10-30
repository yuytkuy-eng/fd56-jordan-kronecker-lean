/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.AllPolynomialCoefficients
import FD56.Hilbert.PolynomialDeformationKernelBound
import FD56.LinearAlgebra.PolynomialTailKernelResidue

/-! Divisibility of specialized polynomial kernel vectors bounds the
dimension of a bounded kernel over the deformation's fraction field. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K F a b : Type*} [Field K] [Field F]
  [Algebra K[X] F] [IsFractionRing K[X] F]
  [Fintype b] [DecidableEq b]

private def shiftedCoefficientMap [DecidableEq K] (d k : ℕ) :
    (b × Fin (d+k+1) → K) →ₗ[K] (b → BoundedPoly K d) := by
  classical
  exact {
    toFun := fun c j => boundedPolyOf
      (Polynomial.ofFn (d+1) (fun l => c (j,⟨l.val+k,by omega⟩)))
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _))
    map_add' := fun c e => by
      funext j
      apply Subtype.ext
      exact map_add (Polynomial.ofFn (d+1)) _ _
    map_smul' := fun s c => by
      funext j
      apply Subtype.ext
      exact map_smul (Polynomial.ofFn (d+1)) s _ }

private theorem shiftedCoefficientMap_of_power [DecidableEq K] (d k : ℕ)
    (c : b × Fin (d+k+1) → K) (z : b → K[X])
    (hz : ∀ j, (z j).natDegree≤d)
    (he : coefficientVectorPolynomial (d+k) c=(X : K[X])^k • z) :
    (fun j => (shiftedCoefficientMap d k c j).val)=z := by
  classical
  funext j
  have hc : (fun l : Fin (d+1) => c (j,⟨l.val+k,by omega⟩))=
      Polynomial.toFn (d+1) (z j) := by
    funext l
    have h := congrArg (fun p : K[X] => p.coeff (l.val+k)) (congrFun he j)
    simpa [coefficientVectorPolynomial,Polynomial.toFn,Polynomial.coeff_X_pow_mul,
      show l.val+k<d+k+1 by omega] using h
  change Polynomial.ofFn (d+1) _=z j
  rw [hc]
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := hz j; omega)

theorem polynomial_kernel_finrank_le_of_residue_divisible
    (P : Matrix a b K[X][X]) (A : Matrix a b K[X]) (N k d : ℕ)
    (hmain : P.map (Polynomial.mapRingHom (Polynomial.evalRingHom 0))=(X : K[X])^N • A)
    (hdiv : ∀ H : b → K[X][X], P*ᵥH=0 → (∀ j, (H j).natDegree≤d+k) →
      ∀ j, (X : K[X])^k ∣ (H j).map (Polynomial.evalRingHom 0)) :
    Module.finrank F (polynomialKernelAtDegree
      (P.map (Polynomial.mapRingHom (algebraMap K[X] F))) (d+k)) ≤
      Module.finrank K (polynomialKernelAtDegree A d) := by
  classical
  let M := allPolynomialCoefficientMatrix P (d+k)
  let f := shiftedCoefficientMap (K:=K) (b:=b) d k
  have hshift (c : b × Fin (d+k+1) → K[X]) (hc : M*ᵥc=0) :
      ∃ z : b → K[X], A*ᵥz=0 ∧
        (fun j => (f (fun jl => (c jl).eval 0) j).val)=z ∧
        coefficientVectorPolynomial (d+k) (fun jl => (c jl).eval 0)=(X : K[X])^k • z := by
    let H := coefficientVectorPolynomial (d+k) c
    have hPH : P*ᵥH=0 := (allPolynomialCoefficientMatrix_kernel_iff P (d+k) c).mp hc
    have hdeg : ∀ j, (H j).natDegree≤d+k := coefficientVectorPolynomial_degree (d+k) c
    obtain ⟨z,hz,hzd,hres⟩ := polynomial_kernel_shift_of_residue_divisible
      P A H N k d hmain hPH (hdiv H hPH hdeg) hdeg
    have he : coefficientVectorPolynomial (d+k) (fun jl => (c jl).eval 0)=(X : K[X])^k • z := by
      have hm := coefficientVectorPolynomial_map (d+k) c (Polynomial.evalRingHom 0)
      simp only [Polynomial.coe_evalRingHom] at hm
      exact hm.trans hres
    exact ⟨z,hz,shiftedCoefficientMap_of_power d k _ z hzd he,he⟩
  rw [← all_coefficient_kernel_finrank,allPolynomialCoefficientMatrix_map]
  apply polynomial_deformation_nullity_le_of_residue_map M 0 f (polynomialKernelAtDegree A d)
  · intro c hc
    obtain ⟨z,hz,hfz,_⟩ := hshift c hc
    change A*ᵥ(fun j => (f (fun jl => (c jl).eval 0) j).val)=0
    rw [hfz]
    exact hz
  · intro c hc hf
    obtain ⟨z,_,hfz,hres⟩ := hshift c hc
    have hz : z=0 := by
      rw [← hfz,hf]
      rfl
    rw [hz,smul_zero] at hres
    funext jl
    have h := congrArg (fun p : K[X] => p.coeff jl.2.val) (congrFun hres jl.1)
    simpa [coefficientVectorPolynomial] using h

end FD56
