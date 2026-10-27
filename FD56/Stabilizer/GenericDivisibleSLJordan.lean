/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleSLActiveTrace
import FD56.Stabilizer.RankTwoSLTracedJordan

/-! Complete constant Jordan–Kronecker congruences for positive divisible generic SL pencils. -/

noncomputable section
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K L : Type*} {m : Type} [Field K] [Field L] [IsAlgClosed L]
  [Fintype m] [DecidableEq m]
local instance genericDivisibleSLJordanDecidableEq : DecidableEq L := Classical.decEq L

theorem generic_divisible_sl_jordan_kronecker_decomposition (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L)
    (i₀ : Fin (q+1) × m) :
    let H := (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.mapRingHom φ)
    let f := polynomialPencilOperator H
    ∃ T : Matrix (SLChartInput (Fin (q+1) × m) m i₀)
      (rankTwoSLCanonicalIndex (fun _ : f.Eigenvalues => Fintype.card m-2)) L,
    ∃ S : Matrix (rankTwoSLCanonicalIndex (fun _ : f.Eigenvalues => Fintype.card m-2))
      (SLChartInput (Fin (q+1) × m) m i₀) L,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * ((slKirillovMatrix
        (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m) i₀).map (Polynomial.mapRingHom φ)) * T.map C=
        rankTwoSLCanonicalTarget (fun a : f.Eigenvalues => a.val)
          (fun _ => Fintype.card m-2) := by
  classical
  let M := genericAffineSquare K (Fin (q+1) × m) m
  let P := genericAffineRows K (Fin (q+1) × m) m
  let H := (glKirillovMatrix M P).map (Polynomial.mapRingHom φ)
  let f := polynomialPencilOperator H
  have hcount : Fintype.card f.Eigenvalues=(q+1)*(q+2)*Fintype.card m/2 :=
    generic_divisible_gl_jordan_pole_count q hm φ
  have htwo : 2≤(q+1)*(q+2) := by nlinarith
  have hmD : Fintype.card m≤Fintype.card f.Eigenvalues := by
    have hmul := Nat.mul_le_mul_right (Fintype.card m) htwo
    omega
  letI : Nontrivial f.Eigenvalues := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let a₀ : f.Eigenvalues := Classical.choice inferInstance
  obtain ⟨G,J,c,d,hGJ,hJG,hcong,htrace,hab⟩ := generic_divisible_gl_jordan_active_trace q hm φ
  let M' := M.map (Polynomial.mapRingHom φ)
  let P' := P.map (Polynomial.mapRingHom φ)
  have hGL : glKirillovMatrix M' P'=H := (glKirillovMatrix_map _ M P).symm
  have hcong' : (G.map C).transpose*glKirillovMatrix M' P'*G.map C=
      rankTwoJordanSumTarget (fun a : f.Eigenvalues => a.val) (fun _ => Fintype.card m-2) := by
    rw [hGL]
    exact hcong
  have htrace' (v : rankTwoJordanSumIndex (fun _ : f.Eigenvalues => Fintype.card m-2) → L) :
      slInputTrace L L (G*ᵥv)=∑ a : f.Eigenvalues,
        (c a*v ⟨a,.inl (.inl 0)⟩+d a*v ⟨a,.inl (.inr 1)⟩) := by
    rw [htrace,rankTwoTraceSumCovector_dotProduct]
  obtain ⟨T,S,hTS,hST,hT⟩ := rankTwoSL_canonical_of_sparse_trace M' P' i₀
    (fun a : f.Eigenvalues => a.val) Subtype.val_injective (fun _ => Fintype.card m-2) a₀
    G J hGJ hJG hcong' c d hab htrace'
  refine ⟨T,S,hTS,hST,?_⟩
  rw [slKirillovMatrix_map]
  exact hT

end FD56
