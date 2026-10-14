# Proof scope and correspondence with Lean

This document maps the [English proof](../arbitrary-rings.tex) to checked Lean
declarations. It distinguishes the mathematical statement proved by the public
entry point, the different representations used internally, and supplementary
claims that have not been formalized. The map was checked against the sources
on October 13, 2026.

## What is self-contained

The note introduces tensors as
coefficient arrays, explains rank as the number of bilinear products, and
defines restrictions, direct sums, character values and profiles at their
first use. Familiar background theorems are cited rather than reproved.

The note gives the integral constructions, the discrete profile argument, and
the conversion from an integer rank decomposition to strict ring circuits.
It assumes elementary finite free module and determinant algebra, existence
of finite fields of each prime-power order, and standard real analysis,
including Fekete's lemma and Stirling's estimate.

Its specialized external input is the abstract Strassen spectral rank theorem.
The note states the required semiring and preorder hypotheses and checks them
for the unit-admitting integer tensor semiring. The citation is
[Zuiddam's updated dissertation](https://staff.fnwi.uva.nl/j.zuiddam/diss/diss_v2.pdf),
Theorem 2.13, Corollary 2.14, and Theorem 2.16. The rank formula is applied to
nonzero tensors that dominate the unit; the zero tensor is treated directly.
The note is self-contained relative to these stated inputs. It does not
reprove the abstract spectral theorem.

For background that can be consulted while reading:

- Bürgisser, Clausen and Shokrollahi, *Algebraic Complexity Theory*,
  [Chapter 14](https://link.springer.com/chapter/10.1007/978-3-662-03338-8_14)
  on multiplicative and bilinear complexity and
  [Chapter 15](https://link.springer.com/chapter/10.1007/978-3-662-03338-8_15)
  on asymptotic matrix multiplication. Their field setting supplies the
  background; the integer and arbitrary-ring adaptations are proved here.
- Lidl and Niederreiter, *Finite Fields*,
  [Chapter 2](https://www.cambridge.org/core/books/abs/finite-fields/structure-of-finite-fields/B800DF02E1774853AABCBF9129A24C7D)
  on finite-field existence, bases, traces and norms.
- Zuiddam's dissertation, Chapter 2, especially §§2.3 and 2.7–2.9, for the
  abstract spectral theory used in the note.

Lean proves the integral spectral upper bound and equality using the bundled
generic separation and fixed point development. It does not take spectral
duality or the profile laws as additional axioms. Its dependency chain uses
finite separation, normalized additive states, compactness, and the bundled
Brouwer proof. These foundations and mathlib have their own proofs rather than
being reproduced in the English note. The audited main results use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Conventions and exact statement

- A coefficient tensor is a function on three finite coordinate sets. The
  notation in the note denotes the corresponding finite free module tensor.
  A restriction matrix has target rows and source columns.
- The note's $A\geq_{\mathbb Z}B$ means that $B$ is obtained from $A$. In Lean
  this is `TS.IsRestriction B A`, or `[B] ≤ [A]` on tensor classes. Here `TS`
  abbreviates `OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring`;
  `AS` abbreviates `OAI.MatrixMultiplication.AuxiliarySeparation`.
- The spectrum in the note is a set of monotone normalized homomorphisms to
  nonnegative reals. Lean uses
  `Matmul.IntegralSpectrum.Character` together with `Monotone χ`: the
  homomorphism has codomain `ℝ`, and nonnegativity follows from monotonicity.
- Lean's asymptotic rank is zero on zero and otherwise the exponential of the
  infimum of normalized logarithmic power ranks. The note uses this definition
  too, and explains its equivalence to the usual limit using Fekete's lemma.
  That limit conversion is standard mathematical background, not a separate
  theorem proved in these local Lean files.
- Lean extends each spectral character to arbitrary integer tensors through
  $\widehat\lambda(T)=\lambda(T\oplus1)-1$. This supports intermediate
  coefficient constructions without requiring every tensor to admit the unit.
  It agrees with the original character on admitted tensors; no faithfulness
  assumption is added.
- $V,U$ in the note are `Matmul.ProfileValues.rawV`, `rawU`; $a_0,b_0$ are
  `Matmul.ProfileValues.a`, `b`. The normalized $P,Q$ are
  `Matmul.IntegerProfileLaws.poweredV`, `poweredU`.
- The note's output coefficient $\gamma_{ih,\ell}$ is
  `alg.output ℓ (h,i)`. The third matrix tensor leg is indexed cyclically as
  $(h,i)$. Its input coefficients are `alg.left ℓ (i,j)` and
  `alg.right ℓ (j,h)`.

The public theorem is
`Matmul.RectangularPrograms.rectangular_multiplication_programs` in
[RectangularPrograms.lean](Matmul/RectangularPrograms.lean#L161).
Its existential circuit family and positive constant precede the quantifier
over `R : Type u` with `[NonUnitalRing R]`. The theorem is universe-polymorphic;
its circuit syntax and integer base scheme do not contain the ring. Correctness
holds at every natural input size, and the cost bound holds for every $n\geq1$.
The English statement restricts both assertions to positive input sizes.

Each addition, negation, or ordered multiplication is one gate. Zero, input
selection, static reindexing, padding and selection of stored outputs have
zero arithmetic cost. Composition and bundles retain their computed finite
families for reuse. Integer scalar actions are built from addition and
negation gates. The formal theorem exposes correctness and gate cost; it does
not state a separate bilinearity invariant for arbitrary circuit syntax.
The constructed witness has linear preparation and reconstruction, with
ordered scalar products at its recursive leaves.

## Declaration map

Each row names declarations whose statements and use in the proof chain were
checked. Namespace abbreviations `AS` and `TS` are as defined above.

| English proof step | Lean declarations | Source |
| --- | --- | --- |
| Exact finite rank and actual decomposition | `AS.exactRank_spec` | [IntegerTensor](Matmul/IntegerTensor.lean) |
| Integer restriction and mutual-restriction quotient | `TS.IsRestriction`, `TS.classOf_le_iff`, `TS.classOf_eq_iff` | [IntegerSemiring](Matmul/IntegerSemiring.lean) |
| Unit-admitting semiring | `TS.unitAdmittingSubsemiring`, `TS.UnitTensorClass.one_le_of_ne_zero` | [IntegerSemiring](Matmul/IntegerSemiring.lean) |
| Rank as a diagonal restriction; cofinality | `TS.rankAtMost_iff_isRestriction_scalarTensor`, `TS.UnitTensorClass.le_rank`, `TS.UnitTensorClass.le_nat_mul_of_ne_zero` | [IntegerScalar](Matmul/IntegerScalar.lean) |
| Infimum of logarithmic power ranks | `TS.UnitTensorClass.logRankGrowth` | [AsymptoticLogRank](Matmul/AsymptoticLogRank.lean) |
| Spectral upper bound, equality, and finite power extraction | `Matmul.IntegralSpectrum.asymptoticRank_le_of_character_bound`, `Matmul.IntegralSpectrum.asymptoticRank_eq_sSup_characterValues`, `Matmul.IntegralSpectrum.exists_rank_power_lt` | [IntegralSpectrumDuality](Matmul/IntegralSpectrumDuality.lean) |
| Character extension and agreement on admitted tensors | `Matmul.IntegerCharacterExtension.extendedHom`, `Matmul.IntegralCharacter.ofUnitTensorClassHom_value_eq` | [IntegerCharacterExtension](Matmul/IntegerCharacterExtension.lean) |
| Dot power laws on the three legs | `Matmul.IntegralCharacter.value_dotX`, `Matmul.IntegralCharacter.value_cyclic_dotX`, `Matmul.IntegralCharacter.value_cyclic_cyclic_dotX` | [IntegerCharacter](Matmul/IntegerCharacter.lean) |
| Matrix factorization and character value | `Matmul.MatrixCharacter.tripleDot_matrixTensor`, `Matmul.MatrixCharacter.matrixClass_power_law` | [MatrixCharacter](Matmul/MatrixCharacter.lean) |
| Coefficient tensor, coefficient maps, and powered restriction | `Matmul.PolynomialCoefficient.coefficientTensor_rank`, `Matmul.PolynomialCoefficient.coefficient_restrict_eq`, `Matmul.PolynomialCoefficient.leading_power_restriction` | [PolynomialCoefficient](Matmul/PolynomialCoefficient.lean) |
| Degeneration monotonicity | `Matmul.PolynomialCoefficient.polynomialRestrictionMonotone` | [PolynomialCoefficient](Matmul/PolynomialCoefficient.lean) |
| Vandermonde adjugate decomposition | `Matmul.IntegralConvolution.rankAtMost_det_vandermonde` | [IntegralConvolutionInterpolation](Matmul/IntegralConvolutionInterpolation.lean) |
| Norm adjugate and integer multiplier | `Matmul.IntegralConvolution.exists_mul_eq_norm`, `Matmul.IntegralConvolution.rankAtMost_norm_vandermonde` | [IntegralConvolutionNorm](Matmul/IntegralConvolutionNorm.lean), [IntegralConvolution](Matmul/IntegralConvolution.lean) |
| Reduction of the norm and prime-avoiding nodes | `Matmul.IntegralConvolution.norm_map_of_compatible_basis`, `Matmul.IntegralConvolution.exists_prime_avoiding_nodes` | [IntegralConvolutionReduction](Matmul/IntegralConvolutionReduction.lean), [IntegralConvolutionFiniteField](Matmul/IntegralConvolutionFiniteField.lean) |
| Constant-cost descent after powering | `Matmul.FiniteAlgebraDescent.linearMap_triple_product`, `Matmul.IntegralConvolution.scaled_integer_power_rank_of_base` | [FiniteAlgebraDescent](Matmul/FiniteAlgebraDescent.lean), [IntegralConvolutionPowers](Matmul/IntegralConvolutionPowers.lean) |
| Finite powered-multiplier patch | `Matmul.IntegralConvolutionBezout.finite_bezout_pow_of_prime_cover`, `Matmul.FiniteAlgebraDescent.integer_power_rank_patch` | [IntegralConvolutionBezout](Matmul/IntegralConvolutionBezout.lean), [FiniteAlgebraDescent](Matmul/FiniteAlgebraDescent.lean) |
| Convolution power-rank bound and character bound | `Matmul.IntegralConvolution.exists_pos_power_rank_bound`, `Matmul.ConvolutionCharacter.valueXY_le` | [IntegralConvolution](Matmul/IntegralConvolution.lean), [ConvolutionCharacter](Matmul/ConvolutionCharacter.lean) |
| Separator support, quadratic weights and polynomial shift | `Matmul.IntegralSeparator.weight_eq_square`, `Matmul.IntegralSeparator.exponent_weight_identity` | [IntegralSeparator](Matmul/IntegralSeparator.lean) |
| Separator leading coefficient and direct sum | `Matmul.SharedLegEntropy.branchPolynomial_eq_restrict`, `Matmul.SharedLegEntropy.branchPolynomial_leading`, `Matmul.SharedLegEntropy.separationTarget_eq_product_directSum` | [SharedLegEntropy](Matmul/SharedLegEntropy.lean) |
| Exact type selection and finite comparison | `Matmul.SharedLegEntropy.exactType_power_pullback`, `Matmul.SharedLegEntropy.integral_type_comparison` | [SharedLegEntropy](Matmul/SharedLegEntropy.lean) |
| Type-count limit and rational-to-real continuity | `AS.typeContribution_rate`, `AS.rational_log_tag_of_finite_type_bounds`, `AS.log_tag_of_integral_bounds` | [EntropyAnalytic/Tag](Matmul/EntropyAnalytic/Tag.lean) |
| Shared-leg entropy with both algebraic backends proved | `Matmul.SharedLegEntropyBackend.fullDependent_tag`, `Matmul.SharedLegEntropyBackend.spectralSharedFirst_tag` | [SharedLegEntropyBackend](Matmul/SharedLegEntropyBackend.lean) |
| Unimodular determinant filtration | `Matmul.IntegralDeterminant.polynomialFamily_identity` | [IntegralDeterminant](Matmul/IntegralDeterminant.lean) |
| Three-sector polynomial degeneration | `AS.Sector.polynomial_identity` | [IntegralTripling](Matmul/IntegralTripling.lean) |
| Determinant entropy and its empty-kernel endpoint | `Matmul.DeterminantLogLaws.determinant_log`, `Matmul.DeterminantLogLaws.determinant_endpoint` | [DeterminantLogLaws](Matmul/DeterminantLogLaws.lean) |
| Character-pair orientation identities in the table | `Matmul.IntegerProfileLaws.pairedXY_rawV`, `Matmul.IntegerProfileLaws.pairedXY_rawU`, `Matmul.IntegerProfileLaws.pairedXY_rawU_first`, `Matmul.IntegerProfileLaws.pairedXZ_rawU`, `Matmul.IntegerProfileLaws.pairedXZ_rawV`, `Matmul.IntegerProfileLaws.pairedXZ_rawU_first` | [IntegerProfileLaws](Matmul/IntegerProfileLaws.lean) |
| Actual paired profiles and their concavity | `Matmul.IntegerProfileLaws.pairedXY_second_difference`, `Matmul.IntegerProfileLaws.V_concave_first`, `Matmul.IntegerProfileLaws.V_concave_second`, `Matmul.IntegerProfileLaws.U_concave_second`, `Matmul.IntegerProfileLaws.U_concave_first` | [IntegerProfileLaws](Matmul/IntegerProfileLaws.lean) |
| Coupled and self-tripling inequalities | `Matmul.IntegerProfileLaws.V_tripling`, `Matmul.IntegerProfileLaws.U_tripling`, `Matmul.IntegerProfileLaws.U_self_tripling` | [IntegerProfileLaws](Matmul/IntegerProfileLaws.lean) |
| Small-parameter diagonal bounds | `Matmul.DiscreteSmallParameter.diagonal_Q_le_four_P`, `Matmul.DiscreteSmallParameter.diagonal_P_le_quadratic` | [DiscreteSmallParameter](Matmul/DiscreteSmallParameter.lean) |
| Common row slopes and affine bound | `Matmul.DiscreteSlopes.exists_common_row_slope`, `Matmul.DiscreteSlopes.profile_le_affine_slope` | [DiscreteSlopes](Matmul/DiscreteSlopes.lean) |
| Intercept, normalized slope, and ray gains | `Matmul.DiscreteProfiles.oriented_affine_upper`, `Matmul.DiscreteProfiles.normalized_slope_bounds`, `Matmul.DiscreteProfiles.rectangular_sequence_step` | [DiscreteProfiles](Matmul/DiscreteProfiles.lean) |
| First-coordinate gain from self-tripling | `Matmul.DiscreteFirstIncrement.first_increment_of_self_tripling` | [DiscreteFirstIncrement](Matmul/DiscreteFirstIncrement.lean) |
| Tangent identity and logarithmic potential | `Matmul.DiscreteProfileCap.slopeFraction_tangent_identity`, `Matmul.DiscreteProfileCap.sequence_ratio`, `Matmul.DiscretePotential.growth_coefficient_le` | [DiscreteProfileCap](Matmul/DiscreteProfileCap.lean), [DiscretePotential](Matmul/DiscretePotential.lean) |
| Assemble actual laws and derive the cap/objective | `Matmul.IntegerProfileCap.actualDiscreteData`, `Matmul.IntegerProfileCap.actual_integer_character_cap`, `Matmul.IntegerProfileCap.actual_rectangular_objective_le` | [IntegerProfileCap](Matmul/IntegerProfileCap.lean) |
| Fixed integer base certificate | `Matmul.RectangularRankBridge.SchemeCertificate`, `Matmul.RectangularRankBridge.exists_scheme_certificate` | [RectangularRankBridge](Matmul/RectangularRankBridge.lean) |
| Integer rank decomposition and ordered ring identity | `Matmul.IntegerBilinear.rankAtMost_iff_exists_algorithm`, `Matmul.IntegerBilinear.Algorithm.evaluate_eq_contract`, `Matmul.IntegerBilinear.matrixTensor_contract` | [IntegerBilinear](Matmul/IntegerBilinear.lean) |
| Ordered bilinear identity on rectangular blocks | `Matmul.IntegerBilinear.Algorithm.rectangular_block_correct` | [BilinearMapBridge](Matmul/BilinearMapBridge.lean) |
| Strict syntax, evaluation and cost | `Matmul.UniversalProgram.Circuit`, `Matmul.UniversalProgram.Circuit.eval`, `Matmul.UniversalProgram.Circuit.cost` | [UniversalProgram](Matmul/UniversalProgram.lean) |
| Integer linear stages contain only charged addition/negation | `Matmul.UniversalProgram.zscale_eval`, `Matmul.UniversalProgram.zscale_cost_le`, `Matmul.UniversalProgram.linearCombination_eval`, `Matmul.UniversalProgram.linearCombination_cost_le` | [UniversalProgram](Matmul/UniversalProgram.lean) |
| Recursive correctness and full gate recurrence | `Matmul.UniversalRecursiveProgram.compile_correct`, `Matmul.UniversalRecursiveProgram.compile_cost_le_work`, `Matmul.UniversalRecursiveProgram.compile_cost_bound` | [UniversalRecursiveProgram](Matmul/UniversalRecursiveProgram.lean) |
| Exact scalar multiplication count | `Matmul.UniversalRecursiveProgram.compile_multiplications` | [UniversalRecursiveProgram](Matmul/UniversalRecursiveProgram.lean) |
| Fixed coefficient weight and recurrence solution | `Matmul.UniversalRecursiveAlgorithm.linearWeight`, `Matmul.RecursiveCost.work`, `Matmul.RecursiveCost.work_bound` | [UniversalRecursiveAlgorithm](Matmul/UniversalRecursiveAlgorithm.lean), [RecursiveCost](Matmul/RecursiveCost.lean) |
| Zero-padding correctness and unchanged gate cost | `Matmul.UniversalPaddedProgram.paddedProgram_correct`, `Matmul.UniversalPaddedProgram.paddedProgram_cost` | [UniversalPaddedProgram](Matmul/UniversalPaddedProgram.lean) |
| Rounded inner dimension fits | `Matmul.RectangularPaddingShape.ceil_rpow_le_pow_of_le_pow` | [RectangularPaddingShape](Matmul/RectangularPaddingShape.lean) |
| One positive constant for all positive sizes | `Matmul.RectangularPrograms.all_sizes_of_eventual_bound`, `Matmul.RectangularPrograms.program_cost_bound` | [RectangularPrograms](Matmul/RectangularPrograms.lean) |
| Public rectangular, square and half-rectangular results | `Matmul.RectangularPrograms.rectangular_multiplication_programs`, `Matmul.RectangularPrograms.square_multiplication_programs`, `Matmul.RectangularPrograms.half_rectangular_multiplication_programs` | [RectangularPrograms](Matmul/RectangularPrograms.lean) |

## Equivalent formulations that are not literal copies

- The convolution theorem covers zero dimensions and the zeroth tensor power
  in Lean. The note uses only positive dimensions and positive powers.
- The separator uses labels $1,\ldots,M$ in the note and `Fin M` with `val+1`
  in Lean. Adding $M^2$ to each of the last two weight families gives the
  nonnegative polynomial exponents and leading degree $2M^2$ used by Lean.
- Lean initially puts branch coordinates in common padded spaces and recovers
  dependent spaces by zero extension. The note writes dependent spaces
  directly. This is covered by the dependent entropy theorem in the map.
- The finite separator value bound is $4M-3$. Lean weakens it to $5M$ for the
  type-limit comparison; either bounded ratio gives the same entropy limit.
- The determinant proof uses $d=r-1,e=s-1$ in Lean. Its polynomial family is
  $t\,\mathrm{graded}+t^2\,\mathrm{erased}$. The three-sector family is likewise
  $t\,\mathrm{retained}+t^2\,\mathrm{erased}$. Both are the note's Laurent
  weighting with a harmless overall degree shift.
- For positive $n$ and integer $a\geq2$, Lean's `Nat.log a n + 1` agrees with
  $\lfloor\log_a n\rfloor+1$. Both choose the next strictly larger outer
  base power, even at an exact power. The inner padding can have a growing
  ratio; its actual volume is included in the cost recurrence.
- The paper reserves $\varepsilon/2$ for the base rank and the remaining
  slack for the logarithmic factor. Lean's cost proof chooses half the gap
  between the selected rank exponent and the target exponent. These are
  equivalent uses of positive slack, not identical internal witnesses.

The public dependency path uses the discrete profile and potential modules
above. It does not rely on the alternative homogeneous-profile modules as a
substitute for proving the actual discrete character laws.

## Supplementary material and verification boundary

The convolution flattening equality, universal lower bounds, and the
three-arbitrary-dimensions exponent corollary are supplementary mathematics.
The integral convolution upper bound is formalized, but this project does not
claim a checked theorem for that matching flattening lower bound or for the
three-variable optimization and real-shape approximation. The main public
scope is the symmetric rectangular upper bound, together with square and
half-rectangular upper-bound corollaries.

Finite Python identity checks supplement the general proofs. They do not
establish the general statements. The source hashes and recorded builds are
in [verification.json](verification.json); the public and central intermediate
axiom dependencies are in [Checks/RectangularAxioms.lean](Checks/RectangularAxioms.lean).
The formal result is classical existence of circuits with an arithmetic gate
bound, not extraction of an executable or a bit-complexity/runtime claim.
