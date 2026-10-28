/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ConvolutionDegrees
import FD56.Hilbert.GenericMinimal

/-! The convolution of two balanced auxiliary degree lists has at most three
adjacent degrees. Their multiplicities are the products of the two pairs of
Euclidean-division multiplicities. -/

namespace FD56

private theorem sum_map_degreeConvolution_int (alpha beta : List ℕ) (f : ℕ → ℤ) :
    ((degreeConvolution alpha beta).map f).sum =
      (alpha.map (fun a => (beta.map (fun b => f (a+b+1))).sum)).sum := by
  induction alpha with
  | nil => simp [degreeConvolution]
  | cons a alpha ih =>
    simp only [degreeConvolution,List.flatMap_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]

theorem degreeConvolution_two_level_perm (a b u v R S q : ℕ) :
    ((degreeConvolution
      (List.replicate u (a+1) ++ List.replicate R a)
      (List.replicate v (b+1) ++ List.replicate S b)).map (fun e => e+q)).Perm
        (List.replicate (R*S) (a+b+q+1) ++
          List.replicate (u*S+R*v) (a+b+q+1+1) ++
          List.replicate (u*v) (a+b+q+1+2)) := by
  apply listHilbert_determines_indices
  intro d
  simp only [listHilbert,List.map_map,Function.comp_def]
  rw [sum_map_degreeConvolution_int]
  have h₀ : a+b+1+q=a+b+q+1 := by omega
  have h₁ : a+1+b+1+q=a+b+q+1+1 := by omega
  have h₁' : a+(b+1)+1+q=a+b+q+1+1 := by omega
  have h₂ : a+1+(b+1)+1+q=a+b+q+1+2 := by omega
  simp only [List.map_append,List.map_replicate,List.sum_append,List.sum_replicate,
    smul_eq_mul,h₀,h₁,h₁',h₂,Nat.cast_add,Nat.cast_mul]
  ring_nf
  ring

theorem balanced_degreeConvolution_perm (A B r s q : ℕ) :
    ((degreeConvolution (balancedDegreeList A r) (balancedDegreeList B s)).map
      (fun e => e+q)).Perm
        (List.replicate ((r-A%r)*(s-B%s)) (A/r+B/s+q+1) ++
          List.replicate ((A%r)*(s-B%s)+(r-A%r)*(B%s)) (A/r+B/s+q+1+1) ++
          List.replicate ((A%r)*(B%s)) (A/r+B/s+q+1+2)) := by
  exact degreeConvolution_two_level_perm (A/r) (B/s) (A%r) (B%s)
    (r-A%r) (s-B%s) q

end FD56
