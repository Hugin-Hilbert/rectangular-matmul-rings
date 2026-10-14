# Rectangular matrix multiplication over arbitrary rings: exponent 9/4

A Lean formalization of the rectangular matrix multiplication bound from
[Rectangular matrix multiplication from shared-leg entropy](https://arxiv.org/abs/2610.10494),
extended to every associative ring. The same finite arithmetic circuits work
over noncommutative rings and rings without a multiplicative identity, in any
characteristic.

For every real $k \geq 0$ and $\varepsilon > 0$, the main theorem chooses a
circuit family and a constant $C > 0$ such that multiplication of an
$n \times \lceil n^k \rceil$ matrix by a
$\lceil n^k \rceil \times n$ matrix uses at most
$C n^{f(k)+\varepsilon}$ arithmetic gates for every integer $n \geq 1$, where

$$
f(k)=
\begin{cases}
2, & 0 \leq k \leq \frac12,\\
1+k+\frac{1}{4k}, & k>\frac12.
\end{cases}
$$

Both the circuit family and $C$ are chosen before the ring. The bound includes
additions, negations, and ordered multiplications. Integer coefficients are
implemented by addition and negation gates. In particular, square multiplication
has exponent at most $9/4$, and the case $k=1/2$ has exponent at most $2$, with
arbitrary positive exponent slack in both statements.

## Main results and search terminology

| Result | Arithmetic operation bound, for every $\varepsilon>0$ |
| --- | --- |
| Square matrix multiplication over arbitrary rings | $O(n^{9/4+\varepsilon})$, giving matrix multiplication exponent $\omega\leq 9/4=2.25$ |
| Rectangular matrix multiplication at aspect ratio $k=1/2$ | $O(n^{2+\varepsilon})$ for $n\times\lceil\sqrt n\rceil$ by $\lceil\sqrt n\rceil\times n$ |
| Dual exponent of matrix multiplication | $\alpha\geq 1/2=0.5$, where $\alpha$ is the supremum of aspect exponents admitting $O(n^{2+\varepsilon})$ for every positive $\varepsilon$ |
| General rectangular matrix multiplication | $O(n^{f(k)+\varepsilon})$ for every real $k\geq0$, with $f$ defined above |

These bounds apply to associative rings, noncommutative rings, and nonunital
rings (rings without identity), uniformly in the characteristic. The Lean 4
formal proof uses integral tensor rank, shared-leg entropy, and universal
arithmetic circuits. The bound extends Uznański's rectangular result to rings;
the exponent curve itself is attributed to the source paper above.

中文摘要：任意结合环上的矩形矩阵乘法，包含非交换环和无单位元环；
平方矩阵乘法指数 $\omega\leq9/4=2.25$，对偶指数 $\alpha\geq1/2$。
这里的复杂度为算术操作数，每个上界都允许任意正的指数余量。
仓库提供 Lean 4 形式化证明、论文 PDF 和整数恒等式验证程序。

## Lean theorems

The public entry point is
[RectangularPrograms.lean](formalization/Matmul/RectangularPrograms.lean):

- `Matmul.RectangularPrograms.rectangular_multiplication_programs`
- `Matmul.RectangularPrograms.square_multiplication_programs`
- `Matmul.RectangularPrograms.half_rectangular_multiplication_programs`

The full development contains 94 Lean modules. All modules passed the original
build on October 12, 2026 and the latest publication check on October 14, 2026.
The main theorems and the key intermediate results
depend only on `propext`, `Classical.choice`, and `Quot.sound`; the local sources
contain no `sorry` or custom axiom declarations. See the
[verification record](formalization/verification.json) and
[axiom audit](formalization/Checks/RectangularAxioms.lean).

The proof establishes the existence of finite arithmetic circuits using
classical witnesses. It does not extract an executable matrix multiplication
implementation. The cost measures arithmetic gates, rather than bit complexity
or the runtime of Lean's evaluator. The three arbitrary shape exponents and
lower bounds discussed in the research note are outside the public Lean theorem.

## Build with an existing Lean and mathlib cache

The verified environment uses **Lean 4.33.0-rc1**, **Python 3.10 or later**, and
mathlib commit `79d0395a1825a6264ad5d269e35e60537518955e`, with its compiled
dependencies. Point the runners at an existing installation:

```bash
export MATMUL_LEAN="/path/to/installed/lean/bin/lean"
export MATMUL_PACKAGES="/path/to/existing/project/.lake/packages"

python3 formalization/build_local.py \
  Matmul.RectangularPrograms Checks.RectangularAxioms --jobs 2
```

`MATMUL_PACKAGES` is the parent directory containing `mathlib`, `aesop`,
`batteries`, and the other already compiled packages. Each package normally
provides `.lake/build/lib/lean`. Use the actual Lean executable for the matching
toolchain. The runners call it directly, build only the project sources, and
never install a toolchain, run `lake update`, or download dependencies.

To check every local Lean module:

```bash
python3 formalization/build_local.py --all --jobs 2
```

Detailed cache configuration, proof dependencies, and reproduction instructions
are in [formalization/README.md](formalization/README.md). The source archive
contains no compiled Lean or mathlib artifacts, so building a fresh checkout
requires an existing compiled dependency cache.

## Research note and finite checks

- [Extension notes](extension-notes.md): the integral constructions and proof outline.
- [Research note](arbitrary-rings.pdf) and [LaTeX source](arbitrary-rings.tex).
- [Proof correspondence](formalization/proof-correspondence.md): precise Lean declarations,
  background results, representation conventions, and the supplementary scope.
- [Source provenance](formalization/PROVENANCE.txt): upstream commits and compatibility changes.

The independent finite identity checks require only Python's standard library:

```bash
python3 verify_integral_constructions.py
```

They check 10,615 separator terms, 5,232 tripling terms, 10 determinant bases,
and 252 multiplication slices. These finite checks supplement the general
proofs; the Lean theorem proves the statements for all relevant parameters.

## Prepare a source archive

```bash
python3 prepare_github.py
```

This creates `dist/rectangular-matmul-rings.zip` with the English documentation,
Lean sources, verification tools, research note, and license notices. It excludes
build caches, LaTeX auxiliary files, local agent directories, and upstream
checkouts. Extract the archive to obtain a clean directory ready for a GitHub
repository. Rebuild it after changing any distributed files.

## License and attribution

The research note is by **Yang Zhou and Mingsheng Wang**. Citation metadata
for this repository is provided in [CITATION.cff](CITATION.cff).

The project is distributed under the [Apache License 2.0](LICENSE), with the
fixed point theorem sources retaining their [MIT license](formalization/FixedPointTheorems/MIT_LICENSE).
[NOTICE](NOTICE) and [PROVENANCE.txt](formalization/PROVENANCE.txt) identify reused
sources from OpenAI's `openai/math`, Jeroen Zuiddam's
`omega-nine-quarters-all-fields`, and harfe's `fixed-point-theorems-lean4`.

The rectangular bound originates in Przemysław Uznański's
[arXiv:2610.10494](https://arxiv.org/abs/2610.10494). The formalization reuses
tensor, entropy, and spectral foundations from the cited Lean developments and
adds the integral extension and the discrete rectangular analysis.
