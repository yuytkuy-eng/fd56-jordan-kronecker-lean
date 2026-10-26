/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.PolynomialMatrix

/-! Exact polynomial chains for a seventeen-state, five-row affine witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def seventeenFiveM : Matrix (Fin 17) (Fin 17) K[X] :=
  ![![0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def seventeenFiveP : Matrix (Fin 5) (Fin 17) K[X] :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, X, 0, 0, 0, 0, 0],
    ![0, X, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, X, 0, 0, 0, 0, X, 0, 1, 0, 0, 0, 0, 0],
    ![X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]]

def seventeenFiveV0Coefficients : Matrix (Fin 17) (Fin 2) (List ℤ) :=
  fun i j => (([
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 2]],
    [[0, 0, 0, 0, 0, 0, 4, 0, -8, -6, 0, 2, -4, -2, 2, 6, 8, -2, -4], [0, 0, 0, 0, 0, 4, 8, -4, -8, 0, 0, -8, 0, 0, 0, 6, 4, -2, -2]],
    [[0, 0, 0, 0, 0, -4, 0, 8, 4, 0, -2, 4, 2, -2, -6, -8, 2, 4], [0, 0, 0, 0, -4, -8, 4, 8, -2, 0, 8, 0, 0, 0, -6, -4, 2, 2]],
    [[0, 0, 0, 0, 2, 0, -4, -2, 0, 0, -2, 0, 4, 4, 4, -2, -4], [0, 0, 0, 2, 4, -2, -4, 0, -2, -6, 0, 2, 2, 4, 2, -2, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, -6, -2, 0, 2, 4], [0, 0, 0, 0, 0, 0, 0, 4, 4, 0, -4, -4, -2, 0, 2, 2]],
    [[0, 0, -2, 0, 4, 2, 0, -4, 0, 6, 8, -2, 0, -2, -4], [0, 0, -4, 0, 6, 2, -6, -4, -2, 6, 6, 0, 0, -2, -2]],
    [[0, 2, 0, -4, -2, 0, 4, 0, -6, -6, 2, 0, 2], [0, 4, 0, -6, -2, 4, 4, 2, -6, -4, 0, 0, 2]],
    [[-1, 0, 2, 1, 0, -2, 0, 3, 4, -1, -4, -4, 1, 1, -2, -1, 1, 3, 4, -1, -2], [-2, 0, 3, 1, -2, -2, -1, 5, 4, -2, -4, -1, 1, -4, 0, 0, 0, 3, 2, -1, -1]],
    [[0, 0, 0, 0, 0, 0, 0, -4, 0, 8, 6, 0, -2, 4, 2, -2, -6, -8, 2, 4], [0, 0, 0, 0, 0, 0, -4, -8, 4, 8, 0, 0, 8, 0, 0, 0, -6, -4, 2, 2]],
    [[0, 0, 0, 0, 0, 0, 2, 0, -4, -6, 0, 6, 4, 4, -2, -4], [0, 0, 0, 0, 0, 4, 4, -4, -8, -4, 2, 4, 4, 2, -2, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 4, 0, -4, -6, -6, 0, 6, 4], [0, 0, 0, 0, -2, 0, 2, 4, 6, 0, -6, -4, -4, 0, 4, 2]],
    [[0, 0, 0, 0, 0, 0, 0, -2, 0, 2, 6, 2, 0, -2, -4], [0, 0, 0, 0, 0, 0, -4, -4, 0, 4, 4, 2, 0, -2, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [0, 0, 0, 0, 0, 2, 0, 0, 0, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0]],
    [[0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2]]]).getD i.val []).getD j.val []

def seventeenFiveV0 : Matrix (Fin 17) (Fin 2) K[X] :=
  fun i j => integerPolynomial (seventeenFiveV0Coefficients i j)

def seventeenFiveV1Coefficients : Matrix (Fin 17) (Fin 2) (List ℤ) :=
  fun i j => (([
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2]],
    [[0, 0, 0, 0, 0, -2, 0, 4, 2, 0, -2, 2, 2, 2, -2, -4], [0, 0, 0, 0, -2, -4, 2, 4, -2, -2, 2, 0, 2, 2, -2, -2]],
    [[0, 0, 0, 0, 2, 0, -4, -2, 0, 2, -2, -2, -2, 2, 4], [0, 0, 0, 2, 4, -2, -4, 0, 2, -2, 0, -2, -2, 2, 2]],
    [[0, 0, 0, -2, 0, 4, 2, 0, -2, 0, 4, 2, -4], [0, 0, 0, -4, 0, 6, 2, -2, 0, -2, 2, 2, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -4], [0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, -2]],
    [[0, 1, 0, -2, -1, 0, 2, 0, -3, -2, 1, -4, -2, 1, 1, -2, -1, 1, 3, 4, -1, -2], [0, 2, 0, -3, -1, 2, 2, 1, -1, 0, -2, -4, 1, 1, -4, 0, 0, 0, 3, 2, -1, -1]],
    [[-1, 0, 2, 1, 0, -2, 0, 3, 0, -1, 4, 2, 1, -1, 2, 1, -1, -3, -4, 1, 2], [-2, 0, 3, 1, -2, -2, -1, 1, -4, 2, 4, -1, 1, 4, 0, 0, 0, -3, -2, 1, 1]],
    [[0, 0, 0, 0, 0, 0, 0, -2, 0, 4, 0, 0, 4, 8, 6, -4, -10, -8, 2, 4], [0, 0, 0, 0, 0, 0, 0, -4, 0, 0, -4, 2, 12, 4, 2, -2, -8, -4, 2, 2]],
    [[0, 0, 0, 0, 0, 0, 2, 0, -4, -2, 0, 2, -2, -2, -2, 2, 4], [0, 0, 0, 0, 0, 2, 4, -2, -4, 2, 2, -2, 0, -2, -2, 2, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, -4, 0, 4], [0, 0, 0, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0, 2]],
    [[0, 0, 0, 0, 0, 0, 0, -2, 0, 2, 2, 2, 0, -2, -4], [0, 0, 0, 0, 0, 0, -2, -4, 0, 4, 2, 2, 0, -2, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 4], [0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
    [[0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
    [[0], [0]]]).getD i.val []).getD j.val []

def seventeenFiveV1 : Matrix (Fin 17) (Fin 2) K[X] :=
  fun i j => integerPolynomial (seventeenFiveV1Coefficients i j)

def seventeenFiveV2Coefficients : Matrix (Fin 17) (Fin 2) (List ℤ) :=
  fun i j => (([
    [[0], [0, 0, 0, 0, 0, 0, 0, 0, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, -2, 4], [0, 0, 0, 2, 0, -2, 2, 2, 0, -2, -2, 0, 0, 0, 2]],
    [[0, 0, 0, -2, 0, 4, 2, 0, -2, 0, 4, 4, -4, 0, 0, -4], [0, 0, 0, -4, 0, 6, 2, -4, 0, -2, 2, 4, -2, 0, 0, -2]],
    [[0, 0, 1, 0, -2, -1, 0, 2, 0, -3, 0, 1, -4, -2, -3, 1, -2, -1, 1, 3, 4, -1, -2], [0, 0, 2, 0, -3, -1, 0, 2, 1, -1, 2, -2, -4, 1, -1, -4, 0, 0, 0, 3, 2, -1, -1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 2]],
    [[-1, 0, 2, 1, 0, -2, 0, 3, -2, -1, 8, 2, 1, 3, 10, 7, -5, -13, -12, 3, 6], [-2, 0, 3, 1, -2, -2, -1, 1, -8, 2, 4, -5, 3, 16, 4, 2, -2, -11, -6, 3, 3]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 6, 6, 4, -6, -8, -4, 2, 4], [0, 0, 0, 0, 0, 0, 2, 0, -2, -4, -2, 4, 10, 4, 0, -4, -6, -2, 2, 2]],
    [[0, 0, 0, 0, 0, 0, 2, 0, -4, 0, 0, 0, -2, -6, -2, 6, 4], [0, 0, 0, 0, 0, 0, 4, 0, -4, 4, 2, -4, 0, -4, -2, 4, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 2, -4], [0, 0, 0, 0, -2, 0, 2, -2, -2, 0, 2, 2, 0, 0, 0, -2]],
    [[0, 0, 0, 0, 0, 0, 0, -2, 0, 2, 0, 2, 0, -2], [0, 0, 0, 0, 0, 0, 0, -4, 0, 4, 0, 2, 0, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -2]],
    [[0], [0, 0, 0, 0, 0, 0, 0, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]],
    [[0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
    [[0], [0]],
    [[0], [0]]]).getD i.val []).getD j.val []

def seventeenFiveV2 : Matrix (Fin 17) (Fin 2) K[X] :=
  fun i j => integerPolynomial (seventeenFiveV2Coefficients i j)

def seventeenFiveV3Coefficients : Matrix (Fin 17) (Fin 2) (List ℤ) :=
  fun i j => (([
    [[0, 0, 0, 0, -2, 0, 4, 2, 0, -2, -2, 6, 4, -6, 4, 0, -4], [0, 0, 0, 2, -4, -2, 8, 4, -4, -2, -4, 2, 4, -2, 2, 0, -2]],
    [[0, 0, 0, -1, 0, 2, 1, 0, 0, 0, 1, 4, -3, -4, -2, -7, 1, -2, -1, 1, 3, 4, -1, -2], [0, 0, 0, -2, 0, 3, 1, -4, 2, -1, 1, 6, -4, -4, 1, -3, -4, 0, 0, 0, 3, 2, -1, -1]],
    [[0, 0, 1, 0, -2, -1, 0, 2, 0, -3, -2, 1, -4, -2, -1, 1, -2, -1, 1, 3, 4, -1, -2], [0, 0, 2, 0, -3, -1, 0, 2, 1, -1, -2, -2, -4, 1, 1, -4, 0, 0, 0, 3, 2, -1, -1]],
    [[0, -1, 0, 2, 1, 0, -2, 0, 3, -4, -1, 8, 2, 3, 3, 10, 7, -5, -13, -12, 3, 6], [0, -2, 0, 3, 1, -2, -2, -1, 1, -12, 2, 4, -5, 5, 16, 4, 2, -2, -11, -6, 3, 3]],
    [[-1, 0, 2, 1, 0, -2, 0, 3, -2, -1, 8, 0, 1, 9, 16, 11, -11, -21, -16, 5, 10], [-2, 0, 3, 1, -2, -2, -1, 3, -8, 0, 0, -7, 7, 26, 8, 2, -6, -17, -8, 5, 5]],
    [[0, 0, 0, 0, 0, 0, 0, 2, 0, -4, -2, 0, 6, 4, -2, -8, -2, 0, 2, 4], [0, 0, 0, 0, 0, 0, 2, 4, -2, -8, 2, 6, 6, 4, -4, -6, -2, 0, 2, 2]],
    [[0, 0, 0, 0, 0, 0, 2, 0, -4, 0, 0, 0, 0, -8, -2, 8], [0, 0, 0, 0, 0, -2, 4, 2, -6, 2, 2, -2, 2, -4, -2, 4]],
    [[0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 2, 2, 0, 0, 0, -4], [0, 0, 0, 0, -2, 0, 2, -2, -6, 0, 6, 2, 2, 0, -2, -2]],
    [[0, 0, 0, 0, 0, 0, 0, -2, 0, 2, 0, 2, 0, -2, 4], [0, 0, 0, 0, 0, 0, 2, -4, 0, 4, 0, 2, 0, -2, 2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 4]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, -2]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6]],
    [[0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
    [[0], [0]],
    [[0], [0]],
    [[0], [0]]]).getD i.val []).getD j.val []

def seventeenFiveV3 : Matrix (Fin 17) (Fin 2) K[X] :=
  fun i j => integerPolynomial (seventeenFiveV3Coefficients i j)

def seventeenFiveTerminalCoefficients : Matrix (Fin 5) (Fin 2) (List ℤ) :=
  ![![[0, 0, 0, 0, -2, 0, 4, 2, 0, -2, -2, 8, 4, -6, 4, 0, -4], [0, 0, 0, 2, -4, -2, 8, 4, -4, -2, -4, 8, 4, -2, 2, 0, -2]],
    ![[-1, 0, 2, 1, 0, -2, 0, 3, -2, -1, 8, 0, 3, 9, 16, 11, -11, -21, -16, 5, 10], [-2, 0, 3, 1, -2, -2, -1, 3, -6, 0, 0, -7, 11, 26, 8, 2, -6, -17, -8, 5, 5]],
    ![[0, 0, 0, 0, -1, 0, 2, -1, 0, 2, 0, 3, 4, -5, 0, -2, -7, 1, -2, -1, 1, 3, 4, -1, -2], [0, 0, 0, 0, -2, 0, 5, -3, -4, 6, -1, 3, 6, -6, -2, 1, -3, -4, 0, 0, 0, 3, 2, -1, -1]],
    ![[0, -1, 0, 2, 1, 0, -2, 0, 3, -2, 1, 10, 0, 1, 11, 16, 11, -11, -21, -16, 5, 10], [0, -2, 0, 3, 1, -2, 0, 1, 3, -8, 4, 4, -7, 7, 26, 8, 2, -6, -17, -8, 5, 5]],
    ![[0, 0, 0, 0, 0, -2, 0, 4, 2, 0, -2, -2, 6, 4, -6, 4, 0, -4], [0, 0, 0, 0, 2, -4, -2, 8, 4, -4, -2, -4, 2, 4, -2, 2, 0, -2]]]

def seventeenFiveF : Matrix (Fin 5) (Fin 2) K[X] :=
  fun i j => integerPolynomial (seventeenFiveTerminalCoefficients i j)

theorem seventeenFive_step0 : seventeenFiveM (K := K) * seventeenFiveV0 = seventeenFiveV1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveM,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    norm_num [seventeenFiveV0,seventeenFiveV1,
      seventeenFiveV0Coefficients,seventeenFiveV1Coefficients,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_step1 : seventeenFiveM (K := K) * seventeenFiveV1 = seventeenFiveV2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveM,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    norm_num [seventeenFiveV1,seventeenFiveV2,
      seventeenFiveV1Coefficients,seventeenFiveV2Coefficients,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_step2 : seventeenFiveM (K := K) * seventeenFiveV2 = seventeenFiveV3 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveM,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    norm_num [seventeenFiveV2,seventeenFiveV3,
      seventeenFiveV2Coefficients,seventeenFiveV3Coefficients,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_output0 : seventeenFiveP (K := K) * seventeenFiveV0 (K := K) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveP,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    norm_num [seventeenFiveV0,seventeenFiveV0Coefficients,
      seventeenFiveF,seventeenFiveTerminalCoefficients,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_output1 : seventeenFiveP (K := K) * seventeenFiveV1 (K := K) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveP,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    norm_num [seventeenFiveV1,seventeenFiveV1Coefficients,
      seventeenFiveF,seventeenFiveTerminalCoefficients,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_output2 : seventeenFiveP (K := K) * seventeenFiveV2 (K := K) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveP,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    norm_num [seventeenFiveV2,seventeenFiveV2Coefficients,
      seventeenFiveF,seventeenFiveTerminalCoefficients,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_output3 : seventeenFiveP (K := K) * seventeenFiveV3 (K := K) = seventeenFiveF := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveP,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    norm_num [seventeenFiveV3,seventeenFiveV3Coefficients,
      seventeenFiveF,seventeenFiveTerminalCoefficients,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_M_degree : DegreeBound (seventeenFiveM (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [seventeenFiveM,Polynomial.natDegree_X])

theorem seventeenFive_P_degree : DegreeBound (seventeenFiveP (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [seventeenFiveP,Polynomial.natDegree_X])

end FD56
