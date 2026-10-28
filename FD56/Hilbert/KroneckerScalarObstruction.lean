/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BidiagonalScalarObstruction
import FD56.Hilbert.KroneckerScalarForcing

/-! At every degree, scalar forcing for a pure Kronecker pencil is exactly
the kernel of the signed Hankel rows of its constant covector. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem kronecker_scalar_forcing_iff (e : ι → ℕ)
    (a : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K)
    (ha : ∀ i j, a ⟨i,Sum.inr j⟩=0) (d : ℕ)
    (c : K[X]) (hc : c.natDegree≤d+1) :
    (∃ z : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K[X],
      (∀ k, (z k).natDegree≤d) ∧
      Matrix.blockDiagonal' (fun i => kroneckerBlockPencil (K:=K) (e i)) *ᵥ z=
        c • (fun k => C (a k)) ∧ (fun k => C (a k)) ⬝ᵥ z=0) ↔
    ∀ (i : ι) (r : Fin (e i-(d+1))),
      (∑ s : Fin (d+2), (-1:K)^s.val*a ⟨i,Sum.inl ⟨r.val+s.val,by
        have := r.isLt; have := s.isLt; omega⟩⟩*c.coeff s.val)=0 := by
  constructor
  · rintro ⟨z,hz,hforce,_⟩ i
    apply (bidiagonal_scalar_lift_iff (e i) d (fun j => a ⟨i,Sum.inl j⟩) c hc).mp
    refine ⟨fun j => z ⟨i,Sum.inr j⟩,fun j => hz _,?_⟩
    funext j
    have h := congrFun hforce ⟨i,Sum.inl j⟩
    rw [blockDiagonal_mulVec] at h
    simpa [kroneckerBlockPencil,Matrix.fromBlocks_mulVec] using h
  · intro h
    have hlift (i : ι) : ∃ v : Fin (e i+1) → K[X],
        (∀ j, (v j).natDegree≤d) ∧
        bidiagonalPencil (e i) *ᵥ v=fun j => c*C (a ⟨i,Sum.inl j⟩) :=
      (bidiagonal_scalar_lift_iff (e i) d (fun j => a ⟨i,Sum.inl j⟩) c hc).mpr (h i)
    choose v hv hmul using hlift
    refine ⟨fun k => Sum.elim (fun _ => 0) (v k.1) k.2,?_,?_,?_⟩
    · rintro ⟨i,j|j⟩
      · simp
      · exact hv i j
    · funext ⟨i,j⟩
      rw [blockDiagonal_mulVec]
      cases j with
      | inl j =>
        simpa [kroneckerBlockPencil,Matrix.fromBlocks_mulVec] using congrFun (hmul i) j
      | inr j => simp [kroneckerBlockPencil,Matrix.fromBlocks_mulVec,ha,Matrix.mulVec,dotProduct]
    · simp [dotProduct,Fintype.sum_sigma,Fintype.sum_sum_type,ha]

end FD56
