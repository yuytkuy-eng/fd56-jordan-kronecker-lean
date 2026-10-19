# Formalization status

This repository formalizes the low-degree obstruction and numerical deductions associated with the manuscript. It does not yet establish the complete generic Jordan–Kronecker classification.

## Constructive kernel argument

The proof constructs two linear maps between finite-dimensional spaces of truncated polynomials. The first has 33k unknown coefficients and 32k equations; the second has 56k unknown coefficients and 55k equations. Rank-nullity supplies nonzero solutions. Lean then checks the rank-one product, its nonvanishing, all stabilizer equations, the trace identity, and the degree bounds.

## Full SL radical and Hilbert obstruction

`TraceZeroStabilizer` describes a trace-zero GL stabilizer. It is a subspace of the full SL radical, not its definition.

`SLRadical` is defined by the Kirillov trace pairing against every trace-zero test matrix and every translation component. `strict_stabilizer_mem_radical` proves the required inclusion.

`slHilbert M P d` is the dimension over the coefficient field of the actual full radical restricted to polynomial pairs of degree at most d. `HasHilbertProfile M P e` asserts equality with the sum of `(d + 1 − e i)` for every d, using truncated subtraction in the natural numbers. A list is balanced when any two entries differ by at most one.

For the family under consideration, `family_slHilbert_five_pos` proves that the actual dimension at degree five is positive. Every balanced list of length 15k² + 1 and sum 97k² − 1 has all entries at least six. Its profile therefore vanishes at degree five. `family_no_balanced_profile` proves the contradiction.

## Arithmetic results

`glFormula`, `slFormula`, and `familyFormula` are computable candidate lists. Their checked arithmetic does not identify them with the actual generic spectra.

For the family list with k² copies of 5, 6k² + 8 copies of 6, and 8k² − 7 copies of 7, the code proves its length, index sum, total block dimension, and failure of balancedness. It checks the six cases (4,3), (8,5), (11,8), (16,7), (64,28), and (43,10) by kernel-checked computation.

The Hilbert arithmetic module proves the two numerical branches of the maximum formula and the Hilbert function identity for balanced lists. The geometric derivation of that maximum formula remains open in this formalization.

## Additional algebraic bridges

`slRadical_iff_equations` proves that membership in the full SL radical is equivalent to trace X = 0, P X = 0, and M X - X M = U P + c I for some polynomial c. This equivalence is derived from the trace pairing; it is not an additional hypothesis.

`hyperplane_radical_finrank` proves that restricting an alternating form on a finite-dimensional vector space to the kernel of a nonzero functional increases the radical dimension by one, provided the original radical lies in that hyperplane. The theorem is abstract linear algebra; applying it to the generic matrix family requires further work.

`listHilbert_determines_indices` proves that equality of the functions sum max(0, d + 1 - e) at all nonnegative degrees determines the finite index lists up to permutation. This does not yet identify the actual polynomial radical with such a profile.

## Remaining work

1. Jordan–Kronecker decomposition and its full relationship with polynomial minimal bases and Hilbert functions.
2. Rank-open loci, codimension estimates for bad loci, and genericity on projective lines.
3. Complete GL polynomial kernel bases for arbitrary parameters and predictable-degree properties.
4. Steiner bundles on the first Hirzebruch surface and balancedness of the auxiliary degree lists.
5. The required application of the Coskun–Huizenga theorem.
6. The Grassmannian extension model, generic extension classes, and realization by the matrix family.
7. Generic Hankel maximal rank and the geometric Hilbert maximum formula.
8. The complete generic GL/SL classification and the associated Zariski-open conditions.

These steps are not introduced as axioms or placeholder proofs. A claim that the entire manuscript has been verified by Lean would exceed the present scope.
