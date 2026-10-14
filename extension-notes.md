# Extending shared-leg entropy to arbitrary rings

This note explains the integral argument behind the Lean formalization of the rectangular matrix multiplication bound in [Przemysław Uznański's *Rectangular matrix multiplication from shared-leg entropy*](https://arxiv.org/html/2610.10494v1). The detailed mathematical proof is in [arbitrary-rings.pdf](arbitrary-rings.pdf), with [LaTeX source](arbitrary-rings.tex). For exact Lean declarations and representation conventions, see [proof-correspondence.md](formalization/proof-correspondence.md); build instructions are in [formalization/README.md](formalization/README.md).

## Result and scope

Fix $k\geq 0$ and $\varepsilon>0$. There is a family of finite arithmetic circuits computing the product of an $n\times\lceil n^k\rceil$ matrix and a $\lceil n^k\rceil\times n$ matrix, using

$$
O_{k,\varepsilon}\bigl(n^{f(k)+\varepsilon}\bigr),\qquad
f(k)=
\begin{cases}
2,&0\leq k\leq \tfrac12,\\
1+k+\dfrac{1}{4k},&k>\tfrac12.
\end{cases}
$$

The same circuit family works over **every associative ring**, including noncommutative rings, rings without a multiplicative identity, rings with zero divisors, and rings of any characteristic. Its gates use addition, negation, and multiplication. The circuits and the bounding constant are chosen before the ring, and the bound holds for every $n\geq1$.

The Lean entry point is [`rectangular_multiplication_programs`](formalization/Matmul/RectangularPrograms.lean). The same file contains the square $9/4+\varepsilon$ and half-rectangular $2+\varepsilon$ corollaries. These are exponent bounds with arbitrary positive slack; they do **not** assert the exact bounds $O(n^{f(k)})$ without slack.

The proof uses standard algebra and real analysis, with abstract Strassen spectral rank duality as a stated background theorem whose hypotheses are checked for the integer semiring. The integral constructions and discrete profile argument are given in the note. Lean proves its integral duality through the bundled separation and fixed point development. The correspondence map records these different proof presentations.

This is a classical existence proof of a circuit family. It does not extract an executable fast multiplication algorithm or certify the running time of Lean's evaluator.

## Why the argument works integrally

### 1. Use an integer tensor semiring

Work with integer tensors, ordered by restriction using integer linear maps on their three legs, and identify tensors that restrict to one another. For the spectral theorem, use the subsemiring consisting of zero and tensors that restrict to the unit tensor $xyz$ over $\mathbb Z$. It is closed under direct sum and tensor product and satisfies the required Strassen preorder conditions. The unit restriction matters: an arbitrary nonzero integer tensor need not admit it; for example, $2xyz$ does not.

Write $\lambda:\mathcal S\to\mathbb R_{\geq0}$ for a normalized additive and multiplicative valuation that is monotone under integer restriction. Spectral duality turns a bound for all such characters into an asymptotic integer rank bound, and hence a rank certificate for a finite tensor power. This is the interface used to select the base algorithm below.

### 2. Replace degeneration interpolation by coefficient extraction

After shifting Laurent leg maps to polynomials, write the transformed tensor as $t^\ell S+$ higher terms, with $\ell\geq0$. Its $m$-th tensor power has coefficient $S^{\otimes m}$ at degree $m\ell$. Extracting this coefficient is an integer restriction after tensoring with the following tensor on three copies of $\mathbb Z^{d+1}$:

$$
H_d=\sum_{\substack{i,j,k\geq0\\i+j+k=d}}x_i y_j z_k,
\qquad \operatorname{rank}_{\mathbb Z}(H_d)\leq(d+1)^2.
$$

For $d=m\ell$, the extra rank is polynomial in $m$ and disappears after taking $m$-th roots. This proves the spectral monotonicity needed for the integral degenerations.

### 3. Bound convolution over the integers

For

$$
C(r,s)=\sum_{i=0}^{r-1}\sum_{j=0}^{s-1}x_i y_j z_{i+j},
\qquad N=r+s-1,
$$

Choose a commutative algebra $B=\mathbb Z[t]/(g)$ with $g$ monic and $N$ evaluation nodes. Let $V$ be the Vandermonde matrix and $\delta=\det V$. The identity $\operatorname{adj}(V)V=\delta I$ gives a length-$N$ decomposition of $\delta C(r,s)$. Set $E=\operatorname{Norm}_B(\delta)\in\mathbb Z$, the determinant of multiplication by $\delta$. Its adjugate supplies $\gamma\delta=E\cdot1_B$, so $EC(r,s)$ has the same decomposition length. This uses no inversion or localization.

Ordinary integer nodes give a nonzero multiplier $E_0$. For each prime $p\mid E_0$, choose an algebra whose reduction modulo $p$ is a field with at least $N$ elements. Distinct residue nodes make the Vandermonde determinant and its norm nonzero modulo $p$, yielding $E_p$ with $p\nmid E_p$.

Take tensor powers in each fixed auxiliary algebra and then descend once to integers. An algebra of rank $d$ contributes only a constant factor $d^2$. The finitely many multipliers have greatest common divisor one, as do their $m$-th powers. A Bézout combination therefore yields

$$
\operatorname{rank}_{\mathbb Z}\bigl(C(r,s)^{\otimes m}\bigr)
\leq K_{r,s}N^m.
$$

Taking roots gives the bound needed by the separator: $\lambda(C(r,s))\leq N$. Output flattening also supplies the matching lower bound, so integer asymptotic rank is exactly $N$. The auxiliary algebras are proof devices; ring circuits use integer linear combinations and multiplication.

### 4. Replace the shared-leg Fourier projection

Let $M\geq1$ and write the source as $A=\sum_{h=1}^M A_h$, where the sectors share the $X$ leg and have disjoint second and third legs. To give them independent first-leg labels, tensor $A$ with $C(2M-1,2M-1)$. With indices $g,h,u,v\in\{1,\ldots,M\}$, choose convolution coordinates

$$
i=2g-2,\qquad j=u-h+M-1,\qquad \ell=v+h+M-3.
$$

The equation $i+j=\ell$ becomes $u-v+2(g-h)=0$. Weights $g^2$, $hu-h^2$, and $-hv$ sum to $(g-h)^2$ on supported terms. The lowest term consequently forces $g=h$ and $u=v$, producing the separated sectors $\bigoplus_h(A_h\otimes B_X(M))$, where $B_X(M)$ is the rank-$M$ pairing with the first leg fixed.

Convolution has spectral cost at most $4M-3$. Counting fixed-frequency words and taking roots recovers the shared-leg entropy inequality over the integers.

### 5. Prove the parameter bound discretely

The determinant filtration uses unimodular integer changes of basis; the three-sector construction uses integer coordinate maps and weights. These give the required properties of both convolution profiles.

For a character, define its dot parameters by $\lambda(B_i(q))=q^{p_i}$ for positive integers $q$ and $i\in\{X,Y,Z\}$, where $B_i(q)$ is the pairing with leg $i$ fixed. Set $a_0=(p_X+p_Y)/2$ and $b_0=p_Z$. The discrete argument establishes

$$
b_0\leq4a_0(1-a_0),\qquad 0\leq a_0,b_0\leq1.
$$

The zero-parameter endpoints and the easy growth branch are closed first. On an integer ray, both profiles have a common limiting row slope. A tangent bound introduces a term containing its varying normalized value; adding a multiple of the diagonal logarithmic increment cancels that term. Finite harmonic summation then yields the parameter inequality. Optimizing $2a_0+kb_0$ gives $f(k)$. This proof avoids logarithmic homogenization and Arzelà–Ascoli.

The detailed proof gives the character-pair identities for each orientation, the factor-two second-difference estimate from the determinant source, and the two ray increments in their required order. These are the bridges from the actual tensor constructions to the discrete scalar hypotheses; they are assembled formally by `Matmul.IntegerProfileCap.actualDiscreteData`.

### 6. Interpret the circuits over every ring

The matrix character bound and spectral duality select one fixed integer base scheme, with dimensions $a\times b$ by $b\times a$ and decomposition length $\rho$, satisfying

$$
a\geq2,\quad b\geq a^k,\quad \rho\geq\max\{ab,a^2\},\quad
\log_a\rho<f(k)+\varepsilon/2.
$$

First establish its ring correctness: each product has a linear combination of entries from the first matrix on the left and one from the second on the right. Expanding the integer coefficient identity preserves this order. The same argument applies to rectangular block multiplication, which is bilinear over $\mathbb Z$.

The remaining cost proof needs only the fixed scheme. At depth $t=\lfloor\log_a n\rfloor+1$,

$$
n<a^t\leq an,\qquad \lceil n^k\rceil\leq b^t.
$$

Let $K_0$ be the sum of $|c|+2$ over the three fixed coefficient arrays and $d=\max\{ab,a^2\}\leq\rho$. The actual circuit satisfies $T(0)=1$ and $T(t+1)\leq\rho T(t)+K_0d^t$, so it has at most $(1+K_0)(t+1)\rho^t$ gates. This charges all coefficient additions and negations and covers the inner padding even when its ratio to $n^k$ grows. The remaining $\varepsilon/2$ absorbs the logarithmic factor, giving one constant for all $n\geq1$, independent of the ring.

## Additional mathematical corollary

For shape exponents sorted as $a\geq b\geq c\geq0$, the proof note gives the following universal exponent upper bounds, again with arbitrary positive slack:

$$
\begin{cases}
a+b,&b\geq2c,\\
a+b+\dfrac{(2c-b)^2}{4(a+c-b)},&b<2c.
\end{cases}
$$

They apply to every permutation of the three shape exponents. This corollary and the discussion of optimality or lower bounds in the mathematical note are **outside the Lean main theorem**. For a fixed ring, any lower bound from dense output size depends on counting output writes in the computational model.

## Checks and sources

[`verify_integral_constructions.py`](verify_integral_constructions.py) checks 10,615 separator terms, 5,232 tripling terms, 10 unimodular determinant bases, and 252 multiplication slices. Run it with `python3 verify_integral_constructions.py`. These finite checks supplement the general proofs; they do not replace them. The Lean theorem uses the proved integer spectral duality, tensor constructions, discrete parameter bound, and strict arithmetic circuit gate count.

The source arguments are Uznański's [rectangular multiplication paper](https://arxiv.org/html/2610.10494v1), OpenAI's [*An upper bound of 9/4 for the matrix multiplication exponent* and Lean development](https://github.com/openai/math/tree/main/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026), and Jeroen Zuiddam's [updated dissertation](https://staff.fnwi.uva.nl/j.zuiddam/diss/diss_v2.pdf), especially §§2.3 and 2.7–2.9 for abstract spectral theory. The integral constructions and discrete proof described above form the extension documented in this repository.
