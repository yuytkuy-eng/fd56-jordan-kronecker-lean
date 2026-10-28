/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericSLScalarHankel

/-! The actual SL lower envelope and its exact maximal-rank obstruction.
The criterion does not assert that the actual Hankel matrix has maximal rank. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

private theorem truncated_degree_envelope {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (d : ℕ) :
    (∑ i, (d+1-e i)) + (d+2-∑ i, (e i-(d+1))) =
      max (∑ i, (d+1-e i)) ((Fintype.card ι+1)*(d+1)+1-∑ i, e i) := by
  have he : (∑ i, (d+1-e i)) + (∑ i, e i) =
      Fintype.card ι*(d+1) + ∑ i, (e i-(d+1)) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i, ((d+1)+(e i-(d+1))) := by
        apply Finset.sum_congr rfl
        intro i _
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hm : (Fintype.card ι+1)*(d+1)+1=Fintype.card ι*(d+1)+(d+2) := by ring
  rw [hm]
  omega

theorem kroneckerScalarObstruction_rank_bounds
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (a : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K) (d : ℕ) :
    Module.finrank K (LinearMap.range (kroneckerScalarObstruction e a d)) ≤
      min (d+2) (∑ i, (e i-(d+1))) := by
  apply le_min
  · simpa only [boundedPoly_finrank] using
      LinearMap.finrank_range_le (kroneckerScalarObstruction e a d)
  · simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_sigma,Fintype.card_fin]
      using Submodule.finrank_le (LinearMap.range (kroneckerScalarObstruction e a d))

theorem generic_sl_hilbert_hankel_rank_criterion
    {K : Type*} [Field K] (n m : ℕ) (hm : 0<m) (hrem : n%m≠0) (i₀ : Fin n) :
    ∃ (r : ℕ) (e : Fin r → ℕ)
      (a : (Σ i, Fin (e i) ⊕ Fin (e i+1)) →
        AffineCoefficientField K (MatrixParameters (Fin n) (Fin m))),
      (List.ofFn e).Perm (glFormula n m) ∧ ∀ d,
      let H := slHilbert (genericAffineSquare K (Fin n) (Fin m))
        (genericAffineRows K (Fin n) (Fin m)) d
      let G := ∑ i, (d+1-e i)
      let R := Module.finrank (AffineCoefficientField K (MatrixParameters (Fin n) (Fin m)))
        (LinearMap.range (kroneckerScalarObstruction e a d))
      let E := max G ((r+1)*(d+1)+1-∑ i, e i)
      H+R=G+(d+2) ∧ E≤H ∧
        (H=E ↔ R=min (d+2) (∑ i, (e i-(d+1)))) := by
  obtain ⟨r,e,a,hperm,hker⟩ := generic_sl_scalar_range_hankel (K:=K) n m hm hrem i₀
  refine ⟨r,e,a,hperm,?_⟩
  intro d
  dsimp only
  let L := AffineCoefficientField K (MatrixParameters (Fin n) (Fin m))
  have hgl : Module.finrank L (polynomialKernelAtDegree
      (glEquationMatrix (genericAffineSquare K (Fin n) (Fin m))
        (genericAffineRows K (Fin n) (Fin m))) d) = ∑ i, (d+1-e i) := by
    rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_nondivisible_gl_formula (K:=K) n m hm hrem).1 d]
    simpa only [List.map_ofFn,List.sum_ofFn] using (hperm.map (fun j => d+1-j)).sum_eq.symm
  have hsl := generic_slHilbert_eq_gl_add_scalar_range (K:=K)
    (n:=Fin n) (m:=Fin m) (by simpa using hm) i₀ d
  rw [hgl,hker d] at hsl
  have hdim := (kroneckerScalarObstruction e a d).finrank_range_add_finrank_ker
  rw [boundedPoly_finrank] at hdim
  have hb := kroneckerScalarObstruction_rank_bounds e a d
  have he := truncated_degree_envelope e d
  simp only [Fintype.card_fin] at he
  omega

end FD56
