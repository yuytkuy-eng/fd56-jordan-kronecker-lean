/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.MiddleSLReduction
import FD56.Stabilizer.MiddleSLDegrees

/-! A one-dimensional polynomial kernel of P turns the full SL scalar
relation into free polynomial coordinates, one for each row of P. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def oneColumnRow {R m : Type*} (e : m → R) : Matrix (Fin 1) m R := fun _ j => e j

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def oneColumnSLScalar (G : Matrix m (Fin 1) K[X]) (e : m → K[X]) : K[X] :=
  -(oneColumnRow e * G) 0 0

omit [DecidableEq m] in
theorem oneColumnSLScalar_relation (G : Matrix m (Fin 1) K[X]) (e : m → K[X]) :
    oneColumnRow e * G = (-oneColumnSLScalar G e) • (1 : Matrix (Fin 1) (Fin 1) K[X]) := by
  funext i j
  fin_cases i
  fin_cases j
  simp [oneColumnSLScalar]

omit [DecidableEq m] in
theorem oneColumnSLScalar_add (G : Matrix m (Fin 1) K[X]) (e f : m → K[X]) :
    oneColumnSLScalar G (e + f) = oneColumnSLScalar G e + oneColumnSLScalar G f := by
  have he : oneColumnRow (e + f) = oneColumnRow e + oneColumnRow f := rfl
  simp only [oneColumnSLScalar, he, Matrix.add_mul, Matrix.add_apply, neg_add]

omit [DecidableEq m] in
theorem oneColumnSLScalar_smul (G : Matrix m (Fin 1) K[X]) (a : K[X]) (e : m → K[X]) :
    oneColumnSLScalar G (a • e) = a • oneColumnSLScalar G e := by
  have he : oneColumnRow (a • e) = a • oneColumnRow e := rfl
  simp only [oneColumnSLScalar, he, Matrix.smul_mul, Matrix.smul_apply, smul_neg]

def oneColumnSLPairMap (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P))) (R : Matrix n m K[X]) :
    (m → K[X]) →ₗ[K[X]] (Matrix n n K[X] × Matrix n m K[X]) where
  toFun e := (middleSLX P B (oneColumnRow e),
    middleSLTranslation M P B R (oneColumnRow e)
      (oneColumnSLScalar (P * M * polynomialKernelBasisMatrix P B) e))
  map_add' e f := by
    have he : oneColumnRow (e + f) = oneColumnRow e + oneColumnRow f := rfl
    apply Prod.ext
    · simp only [middleSLX, he, Matrix.mul_add, Matrix.add_mul, Prod.fst_add]
    · simp only [middleSLTranslation, middleSLX, he, oneColumnSLScalar_add,
        Matrix.mul_add, Matrix.add_mul, add_smul, Prod.snd_add]
      simp only [Matrix.sub_mul, Matrix.add_mul]
      abel
  map_smul' a e := by
    have he : oneColumnRow (a • e) = a • oneColumnRow e := rfl
    apply Prod.ext
    · change middleSLX P B (oneColumnRow (a • e)) = a • middleSLX P B (oneColumnRow e)
      simp only [middleSLX, he, Matrix.mul_smul, Matrix.smul_mul]
    · change middleSLTranslation M P B R (oneColumnRow (a • e))
        (oneColumnSLScalar (P * M * polynomialKernelBasisMatrix P B) (a • e)) =
        a • middleSLTranslation M P B R (oneColumnRow e)
          (oneColumnSLScalar (P * M * polynomialKernelBasisMatrix P B) e)
      simp [middleSLTranslation, middleSLX, he, oneColumnSLScalar_smul,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul]
      rw [← smul_smul, ← smul_sub, ← smul_sub, Matrix.smul_mul]

theorem oneColumnSLPairMap_radical (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) (i₀ : n) (e : m → K[X]) :
    SLRadical M P (oneColumnSLPairMap M P B R e).1 (oneColumnSLPairMap M P B R e).2 := by
  letI : Nonempty n := ⟨i₀⟩
  apply (slRadical_iff_equations M P _ _).mpr
  have hh := middle_sl_reconstruct M P B R hPR (oneColumnRow e)
    (oneColumnSLScalar (P * M * polynomialKernelBasisMatrix P B) e)
    (oneColumnSLScalar_relation _ e)
  exact ⟨hh.1, hh.2.1, _, hh.2.2⟩

def oneColumnSLMap (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) (i₀ : n) :
    (m → K[X]) →ₗ[K[X]] LinearMap.ker (Matrix.toLin' (slEquationMatrix M P i₀)) :=
  ((matrixPairEquiv K[X] K[X] n m).symm.toLinearMap.comp
    (oneColumnSLPairMap M P B R)).codRestrict _ (by
      intro e
      apply (slEquationMatrix_kernel_iff M P i₀ _).mpr
      exact oneColumnSLPairMap_radical M P B R hPR i₀ e)

theorem oneColumnSLMap_bijective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec) (i₀ : n) :
    Function.Bijective (oneColumnSLMap M P B R hPR i₀) := by
  letI : Nonempty n := ⟨i₀⟩
  constructor
  · intro e f h
    have hx := congrArg (fun z : LinearMap.ker (Matrix.toLin' (slEquationMatrix M P i₀)) =>
      (matrixPairEquiv K[X] K[X] n m z.val).1) h
    change middleSLX P B (oneColumnRow e) = middleSLX P B (oneColumnRow f) at hx
    have he := middleSLX_injective P B R hPR hx
    funext j
    exact congrFun (congrFun he 0) j
  · intro z
    let X := (matrixPairEquiv K[X] K[X] n m z.val).1
    let U := (matrixPairEquiv K[X] K[X] n m z.val).2
    have hz : SLRadical M P X U := (slEquationMatrix_kernel_iff M P i₀ z.val).mp z.property
    obtain ⟨E, c, hEG, hXE, hU⟩ := (middle_sl_radical_iff M P B R hPR hG X U).mp hz
    let e : m → K[X] := E 0
    have hE : oneColumnRow e = E := by
      funext i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    have hc : oneColumnSLScalar (P * M * polynomialKernelBasisMatrix P B) e = c := by
      unfold oneColumnSLScalar
      rw [hE, hEG]
      simp
    refine ⟨e, ?_⟩
    apply Subtype.ext
    apply (matrixPairEquiv K[X] K[X] n m).injective
    change (middleSLX P B (oneColumnRow e),
      middleSLTranslation M P B R (oneColumnRow e)
        (oneColumnSLScalar (P * M * polynomialKernelBasisMatrix P B) e)) = (X, U)
    rw [hE, hc, ← hXE, ← hU]

def oneColumnSLKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec) (i₀ : n) :
    (m → K[X]) ≃ₗ[K[X]] LinearMap.ker (Matrix.toLin' (slEquationMatrix M P i₀)) :=
  LinearEquiv.ofBijective (oneColumnSLMap M P B R hPR i₀)
    (oneColumnSLMap_bijective M P B R hPR hG i₀)

def oneColumnSLKernelBasis (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec) (i₀ : n) :
    Basis m K[X] (LinearMap.ker (Matrix.toLin' (slEquationMatrix M P i₀))) :=
  (Pi.basisFun K[X] m).map (oneColumnSLKernelEquiv M P B R hPR hG i₀)

theorem oneColumnSLKernelBasis_pair (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec) (i₀ : n) (j : m) :
    matrixPairEquiv K[X] K[X] n m (oneColumnSLKernelBasis M P B R hPR hG i₀ j).val =
      oneColumnSLPairMap M P B R (Pi.single j 1) := by
  change oneColumnSLPairMap M P B R (Pi.basisFun K[X] m j) = _
  rw [Pi.basisFun_apply]

theorem oneColumnSLKernelBasis_x (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (i₀ : n) (j : m) (x y : n) :
    (oneColumnSLKernelBasis M P B R hPR hG i₀ j).val (Sum.inl (x, y)) =
      polynomialKernelBasisMatrix P B x 0 * P j y := by
  have hh := congrArg (fun z : Matrix n n K[X] × Matrix n m K[X] => z.1 x y)
    (oneColumnSLKernelBasis_pair M P B R hPR hG i₀ j)
  change (oneColumnSLKernelBasis M P B R hPR hG i₀ j).val (Sum.inl (x, y)) =
    (polynomialKernelBasisMatrix P B *
      (show Matrix (Fin 1) m K[X] from fun _ => Pi.single j 1) * P) x y at hh
  rw [middle_one_column_product_single] at hh
  exact hh

theorem oneColumnSLKernelBasis_degree (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a)
    (hBlead : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a)))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (i₀ : n) :
    ∀ z j, (polynomialKernelBasisMatrix (slEquationMatrix M P i₀)
      (oneColumnSLKernelBasis M P B R hPR hG i₀) z j).natDegree ≤ a + 1 := by
  intro z j
  let E : Matrix (Fin 1) m K[X] := oneColumnRow (Pi.single j 1)
  let c := oneColumnSLScalar (P * M * polynomialKernelBasisMatrix P B) (Pi.single j 1)
  have hrel : E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 :=
    oneColumnSLScalar_relation _ _
  have hX : DegreeBound (middleSLX P B E) (a + 1) :=
    middle_one_column_single_degree (polynomialKernelBasisMatrix P B) P a hB hP j
  have hc : c.natDegree ≤ (a + 1) + 1 :=
    middle_scalar_degree M P (polynomialKernelBasisMatrix P B) E (fun _ => a)
      c 0 (a + 1) hM hP hB hBlead hPlead hX hrel
  have hU : DegreeBound (middleSLTranslation M P B R E c) (a + 1) :=
    middle_translation_degree M P (middleSLX P B E) (middleSLTranslation M P B R E c)
      c (a + 1) hM hP hPlead hX hc (middle_sl_reconstruct M P B R hPR E c hrel).2.2
  cases z with
  | inl xy =>
    have hh := congrArg (fun z : Matrix n n K[X] × Matrix n m K[X] => z.1 xy.1 xy.2)
      (oneColumnSLKernelBasis_pair M P B R hPR hG i₀ j)
    change (oneColumnSLKernelBasis M P B R hPR hG i₀ j).val (Sum.inl xy) =
      middleSLX P B E xy.1 xy.2 at hh
    change ((oneColumnSLKernelBasis M P B R hPR hG i₀ j).val (Sum.inl xy)).natDegree ≤ _
    rw [hh]
    exact hX xy.1 xy.2
  | inr xj =>
    have hh := congrArg (fun z : Matrix n n K[X] × Matrix n m K[X] => z.2 xj.1 xj.2)
      (oneColumnSLKernelBasis_pair M P B R hPR hG i₀ j)
    change (oneColumnSLKernelBasis M P B R hPR hG i₀ j).val (Sum.inr xj) =
      middleSLTranslation M P B R E c xj.1 xj.2 at hh
    change ((oneColumnSLKernelBasis M P B R hPR hG i₀ j).val (Sum.inr xj)).natDegree ≤ _
    rw [hh]
    exact hU xj.1 xj.2

theorem oneColumnSLKernelBasis_leading_injective
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : ℕ) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a)
    (hBlead : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a)))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (i₀ : n) :
    Function.Injective (Matrix.mulVec (fun z j =>
      (polynomialKernelBasisMatrix (slEquationMatrix M P i₀)
        (oneColumnSLKernelBasis M P B R hPR hG i₀) z j).coeff (a + 1))) := by
  intro c e h
  apply middle_one_column_product_leading_injective
    (polynomialKernelBasisMatrix P B) P a hB hBlead hP hPlead
  funext xy
  rcases xy with ⟨x, y⟩
  have hh := congrFun h (Sum.inl (x, y))
  simpa only [Matrix.mulVec, dotProduct, polynomialKernelBasisMatrix,
    oneColumnSLKernelBasis_x] using hh

/-- A one-column polynomial kernel of degree a yields card m full SL
minimal indices equal to a + 1. -/
theorem one_column_sl_kernel_hilbert (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis (Fin 1) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a)
    (hBlead : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a)))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (i₀ : n) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (slEquationMatrix M P i₀) d) =
      Fintype.card m * (d + 1 - (a + 1)) := by
  rw [polynomial_kernel_basis_hilbert (slEquationMatrix M P i₀)
    (oneColumnSLKernelBasis M P B R hPR hG i₀) (fun _ => a + 1) d
    (oneColumnSLKernelBasis_degree M P B R hPR hG a hM hP hB hBlead hPlead i₀)
    (oneColumnSLKernelBasis_leading_injective M P B R hPR hG a hP hB hBlead hPlead i₀)]
  simp

end FD56
