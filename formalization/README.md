# Lean formalization of rectangular multiplication over arbitrary rings

The public theorem constructs one family of finite arithmetic circuits for
every real $k \geq 0$ and $\varepsilon > 0$. The circuits compute
$n \times \lceil n^k \rceil$ by $\lceil n^k \rceil \times n$ matrix products over
every `NonUnitalRing`, with at most $C n^{f(k)+\varepsilon}$ gates for every
$n \geq 1$. The family and the constant are independent of the ring.

## Public entry points

[Matmul/RectangularPrograms.lean](Matmul/RectangularPrograms.lean) proves:

| Theorem | Shape | Exponent upper bound |
| --- | --- | --- |
| `rectangular_multiplication_programs` | $n \times \lceil n^k \rceil$ by $\lceil n^k \rceil \times n$ | $f(k)+\varepsilon$ |
| `square_multiplication_programs` | $n \times n$ by $n \times n$ | $9/4+\varepsilon$ |
| `half_rectangular_multiplication_programs` | $n \times \lceil n^{1/2} \rceil$ by $\lceil n^{1/2} \rceil \times n$ | $2+\varepsilon$ |

All three names are in the namespace `Matmul.RectangularPrograms`. Here
$f(k)=2$ for $0 \leq k \leq 1/2$, and $f(k)=1+k+1/(4k)$ for $k>1/2$.

`NonUnitalRing` includes associative rings without an identity. Neither
commutativity nor restrictions on characteristic or zero divisors are assumed.
The multiplication gates preserve the order of the two input factors.

The circuit syntax in [UniversalProgram.lean](Matmul/UniversalProgram.lean)
contains explicit addition, negation, and multiplication gates, together with
wires, zero outputs, and finite composition. Its cost is the sum of the three
arithmetic gate counts. Integer coefficient operations compile to addition and
negation gates. Wires, static index changes, zero padding, and reading stored
values do not contribute arithmetic gates.

The witnesses are classical finite circuit existence proofs. They are not an
extracted executable implementation, and the cost is not an evaluator runtime
or bit complexity bound. The arbitrary three shape exponents and lower bound
discussion in the [research note](../arbitrary-rings.pdf) are supplementary
mathematical statements outside these public Lean entry points.

## Reproduce the build

Run the following commands from the repository root with Python 3.10 or later.
Use the actual executable of an already installed **Lean 4.33.0-rc1** toolchain
and an existing compiled mathlib bundle at commit
`79d0395a1825a6264ad5d269e35e60537518955e`:

```bash
export MATMUL_LEAN="/path/to/installed/lean/bin/lean"
export MATMUL_PACKAGES="/path/to/existing/project/.lake/packages"

python3 formalization/build_local.py \
  Matmul.RectangularPrograms Checks.RectangularAxioms --jobs 2
```

The package directory must include compiled artifacts for mathlib and its
dependencies. The recorded bundle includes `LeanSearchClient`, `importGraph`,
`Qq`, `proofwidgets`, `batteries`, `aesop`, and `plausible` in addition to mathlib.
The existing dependency manifest can be kept in the project that owns the
cache; this repository does not run Lake to fetch or replace it. The exact
verified dependency revisions are recorded in
[dependency-pins.json](dependency-pins.json).

The runners also accept `MATMUL_LEAN_PATH`, an operating system path separated
list of compiled Lean library directories, for caches with a different layout:

```bash
export MATMUL_LEAN_PATH="/path/to/mathlib/lib/lean:/path/to/aesop/lib/lean:/path/to/other/lib/lean"
```

Include all required dependency library directories. The project output
directory is added to the search path automatically. Explicit environment
settings are the recommended way to reproduce the recorded environment;
the runners can also discover existing conventional project package caches
and installed toolchain executables.

To build all 94 local modules:

```bash
python3 formalization/build_local.py --all --jobs 2
```

To recheck the main file after its imports have been built:

```bash
python3 formalization/check_lean.py formalization/Matmul/RectangularPrograms.lean
```

The runners never download dependencies, install a toolchain, or run
`lake update`. They write only project build artifacts under `.lake/build`:

- `lib/lean`: compiled local modules and incremental build signatures.
- `logs`: compiler commands, exit codes, and output.
- `tmp`: temporary compilation outputs.

`--jobs` accepts one to four workers. The builder checks imports before
compilation and reports a missing compiled dependency without fetching it.
Use `--force` to rebuild local modules while retaining the existing dependency
cache. `--help` lists the supported compiler flags.

## Proof dependencies

For the exact declarations, orientation conventions, and equivalent
formulations used by the English proof, see
[proof-correspondence.md](proof-correspondence.md). The map also distinguishes
the supplementary mathematical statements from the public Lean scope.

| Stage | Main modules |
| --- | --- |
| Integral tensor rank and the unit admitting semiring | [IntegerTensor](Matmul/IntegerTensor.lean), [IntegerSemiring](Matmul/IntegerSemiring.lean), [IntegerScalar](Matmul/IntegerScalar.lean) |
| Integral spectral duality and finite power certificates | [IntegralSpectrumDuality](Matmul/IntegralSpectrumDuality.lean) |
| Integral convolution rank bounds | [IntegralConvolution](Matmul/IntegralConvolution.lean) |
| Coefficient extraction and degeneration monotonicity | [PolynomialCoefficient](Matmul/PolynomialCoefficient.lean), [PolynomialPower](Matmul/PolynomialPower.lean) |
| The integral separator and shared leg entropy | [IntegralSeparator](Matmul/IntegralSeparator.lean), [SharedLegEntropyBackend](Matmul/SharedLegEntropyBackend.lean) |
| Determinant filtration and three sector degeneration | [IntegralDeterminant](Matmul/IntegralDeterminant.lean), [IntegralTripling](Matmul/IntegralTripling.lean) |
| Actual character profiles and the parabolic cap | [IntegerProfileLaws](Matmul/IntegerProfileLaws.lean), [IntegerProfileCap](Matmul/IntegerProfileCap.lean), [DiscreteParameterCap](Matmul/DiscreteParameterCap.lean) |
| Rectangular character values and finite integer schemes | [MatrixCharacter](Matmul/MatrixCharacter.lean), [RectangularRankBridge](Matmul/RectangularRankBridge.lean) |
| Strict circuit compilation, recursion, and padding | [UniversalProgram](Matmul/UniversalProgram.lean), [UniversalRecursiveProgram](Matmul/UniversalRecursiveProgram.lean), [UniversalPaddedProgram](Matmul/UniversalPaddedProgram.lean) |
| All positive input sizes and the public results | [RectangularPrograms](Matmul/RectangularPrograms.lean) |

The character cap $b \leq 4a(1-a)$ is proved from the actual integral tensor
constructions. The discrete argument uses common row slopes and a logarithmic
potential; it does not assume the target profile laws or require a
homogenization or compactness theorem.

## Verification and provenance

All 94 local modules passed the original build on October 12, 2026 and the
latest publication check on October 14, 2026. The local
sources contain no `sorry` or custom axiom declarations. The nine results in
[Checks/RectangularAxioms.lean](Checks/RectangularAxioms.lean), including all
public theorems, depend only on `propext`, `Classical.choice`, and `Quot.sound`.

[verification.json](verification.json) records the toolchain, mathlib revision,
main source hash, and axiom audits. [PROVENANCE.txt](PROVENANCE.txt) records the
reused source revisions and licenses. [env-provenance.txt](env-provenance.txt)
records the original dependency bundle and runner checks.
