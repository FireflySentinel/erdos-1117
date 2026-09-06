# Erdős Problem #1117: a bound for the number of maximum modulus points

Preprint answering the second question of
[Erdős Problem #1117](https://www.erdosproblems.com/1117) in the negative: no non-monomial
entire function has $\nu_f(r)\to\infty$.

[Preprint PDF](paper/PROOF.pdf) · [LaTeX source](paper/PROOF.tex) ·
[Formalization notes](FORMALIZATION.md)

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1117
```

## Exact statement

[`Erdos1117.maximum_bound_off_countable_of_global_fiber_bound`](Erdos1117/Main.lean)
proves $\nu_f(r)\le 2k$ outside a countable set of radii, and
`not_tendsto_atTop_of_countable_exceptions` deduces that $\nu_f(r)$ cannot tend to infinity.

Lemma 3.1 and Proposition 4.2 of the manuscript are not proved in Lean, so this is a
partial formalization of Theorem 1.

## AI use disclosure

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition and
did not contribute to the mathematical arguments. The author reviewed the final
manuscript and takes full responsibility for its content.

The Lean formalization was developed with OpenAI Codex (GPT-6).
