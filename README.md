# Erdős Problem #1117: a bound for the number of maximum modulus points

Preprint answering the second question of
[Erdős Problem #1117](https://www.erdosproblems.com/1117) in the negative: no non-monomial
entire function has $\nu_f(r)\to\infty$.

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

## Proof correspondence

| Manuscript argument | Lean source |
|---|---|
| Common real value off a countable set of radii | [FactoredFunction.lean](Erdos1117/FactoredFunction.lean), `maximum_points_common_value_off_countable` |
| Small-product fibre bound | [SmallFiber.lean](Erdos1117/SmallFiber.lean), `small_product_fiber_bound_of_coordinates` |
| Maximum-point injection and the bound off a countable set | [FiberApplication.lean](Erdos1117/FiberApplication.lean), `maximum_bound_off_countable_of_global_fiber_bound` |
| Theorem 1, conditional on the global estimate | [Main.lean](Erdos1117/Main.lean), `theorem_1_1_of_entire` |
| Remark 5.1, sharpness of the factor 2 | [SharpExample.lean](Erdos1117/SharpExample.lean) |

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition and
did not contribute to the mathematical arguments. The author reviewed the final
manuscript and takes full responsibility for its content.

The Lean formalization was developed with OpenAI Codex (GPT-6).
