# Erdős Problem #1117: a bound for the number of maximum modulus points

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22331977.svg)](https://doi.org/10.5281/zenodo.22331977)

Preprint answering the second question of
[Erdős Problem #1117](https://www.erdosproblems.com/1117) in the negative: no non-monomial
entire function has $\nu_f(r)\to\infty$.

**Qiyuan Gu**, University of Chicago

[Preprint PDF](PROOF.pdf) · [LaTeX source](PROOF.tex)

Published version: [v4](https://doi.org/10.5281/zenodo.22333117), 5 September 2026.

Comments and corrections: [email](mailto:phoenix1203@uchicago.edu) or
[issue](https://github.com/FireflySentinel/erdos-1117/issues).

## Abstract

For a non-monomial entire function $f$, let $\nu_f(r)$ be the number of points on $|z|=r$
at which $|f|$ attains its maximum. Write $f(z)=z^m(c_0+c_kz^k+O(z^{k+1}))$, where
$c_0c_k\neq 0$ and $k\ge 1$. We prove that $\nu_f(r)\le 2k$ outside a countable set of
radii. In particular, $\nu_f(r)$ cannot tend to infinity, answering the second question of
Erdős on maximum modulus points. The proof studies the correspondence
$A(z)=\overline{A(\bar w)}$, where $A=zf'/f$, using implicit-function continuation, growth
in a direct tract, and a finite proper map of analytic curves.

## Main theorem

**Theorem 1.** Let $f$ be a nonzero entire function that is not a monomial, and write

$$f(z)=z^m\left(c_0+c_kz^k+O(z^{k+1})\right), \qquad m\ge 0,\quad k\ge 1,\quad c_0c_k\neq 0.$$

There is a countable set $E\subset(0,\infty)$ such that

$$\nu_f(r)\le 2k \qquad (r\notin E).$$

Consequently $\liminf_{r\to\infty}\nu_f(r)\le 2k<\infty$.

Here $k$ is the difference between the degrees of the first two nonzero terms of $f$. The
factor $2$ is attained: for $f=\exp(2z^k-z^{2k})$ there are exactly $2k$ maximum modulus
points for all large $r$.

## The problem

Erdős asked whether a single non-monomial entire function can satisfy
$\limsup_{r\to\infty}\nu_f(r)=\infty$, and whether it can satisfy
$\liminf_{r\to\infty}\nu_f(r)=\infty$.

| | |
|---|---|
| Herzog–Piranian (1968) | the first question: yes |
| Pardo-Simón–Sixsmith ([arXiv:2607.09462](https://arxiv.org/abs/2607.09462), Jul 2026) | such an example can be taken of finite order, in the Eremenko–Lyubich class $\mathcal{B}$ |
| Glücksam–Pardo-Simón ([arXiv:2208.11154](https://arxiv.org/abs/2208.11154)) | an approximate analogue of the second property: many separated arcs on which the modulus is close to its maximum |
| Hayman (1951) | near the origin, the maximum modulus set consists of at most $k$ analytic curves |
| Evdoridou–Pardo-Simón–Sixsmith ([arXiv:2012.07409](https://arxiv.org/abs/2012.07409)) | the exact number of local maximum curves outside an algebraically defined exceptional class; each contains exactly one point of each sufficiently small positive modulus, so $\nu_f(r)\le k$ for small $r$ |
| this preprint | the second question: no |

The bound $2k$ depends on $f$, through the order of vanishing of $zf'/f-m$ at the origin.
It therefore does not conflict with a family of functions whose counts grow without bound;
it rules out a single $f$ with $\nu_f(r)\to\infty$.

## Method

Set $A=zf'/f$. At any radius where $\log M(r,f)$ is differentiable with respect to
$\log r$, all maximum modulus points share the same real value of $A$, so they give points
$(z,\bar z)$ of the complex curve $A(z)=\overline{A(\bar w)}$ with the same values of both
$zw$ and $A(z)$. Continuation of implicit functions, together with growth in a direct tract
(Bergweiler–Rippon–Stallard), controls the branches of that curve near the coordinate axes;
the map $(z,w)\mapsto(zw,A(z))$ is finite and proper off a small locus, and its total fibre
count is bounded by the local degree $k$ at each end. Convexity of $\log M$ in $\log r$
confines the exceptional radii to a countable set.

## AI use disclosure

Generative AI tools were used substantially during the development of this work. OpenAI's
GPT-6, accessed through Codex, was used to develop parts of the proof, including the
logarithmic-derivative formulation, the implicit-function and direct-tract argument, the
finite-map argument, and the sharpness example. It was also used for literature search,
proof checking, and language and LaTeX editing. The author reviewed and verified the
mathematical arguments and references and takes full responsibility for the manuscript.

## Citation

```bibtex
@misc{gu2026erdos1117,
  author       = {Qiyuan Gu},
  title        = {A bound for the number of maximum modulus points},
  year         = {2026},
  doi          = {10.5281/zenodo.22331977},
  howpublished = {Preprint, Zenodo},
  note         = {Erd\H{o}s Problem 1117}
}
```

Problem statement quoted from T. F. Bloom, *Erdős Problem #1117*,
<https://www.erdosproblems.com/1117>.
