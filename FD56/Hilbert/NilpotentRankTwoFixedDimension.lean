/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NilpotentRankTwoJordan

/-! A rank-two nilpotent pencil in dimension 2m has m-2 simple regular blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem nilpotent_rank_two_fixed_dimension_jordan {K n : Type*} [Field K]
    [Fintype n] [DecidableEq n] (m : ℕ) (hdim : Fintype.card n=2*m)
    (B N : Matrix n n K) (a : K)
    (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (hBN : ∀ v, v ⬝ᵥ ((B*N) *ᵥ v)=0)
    (hdet : B.det≠0) (hn : IsNilpotent N)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' N))=2) :
    2≤m ∧
    ∃ T : Matrix n (rankTwoJordanIndex (m-2)) K,
    ∃ U : Matrix (rankTwoJordanIndex (m-2)) n K,
      T*U=1 ∧ U*T=1 ∧
      (T.map C).transpose*((X-C a) • B.map C-(B*N).map C)*T.map C=
        rankTwoJordanPencil a (m-2) := by
  obtain ⟨k,hcard,T,U,hTU,hUT,hcong⟩ :=
    nilpotent_rank_two_jordan_decomposition B N a hB hBN hdet hn hr
  have hk : k=m-2 := by omega
  subst k
  exact ⟨by omega,T,U,hTU,hUT,hcong⟩

end FD56
