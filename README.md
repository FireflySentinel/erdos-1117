# A negative answer to a question of Erdős on maximum modulus points

Preprint answering the second question of
[Erdős Problem #1117](https://www.erdosproblems.com/1117) in the negative: no non-monomial
entire function has $\nu_f(r)\to\infty$.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos1117
```

## Exact statement

[`theorem_1_1_of_entire`](Erdos1117/Main.lean) starts with a nonzero,
non-monomial entire function and extracts its zero order and Taylor gap $k$.
Assuming [`GlobalFibreBound`](Erdos1117/FiberApplication.lean), it proves
`(maximumPoints f r).encard ≤ 2 * k` outside a countable set of positive radii
and at arbitrarily large radii. The use of `encard` includes finiteness in the bound.

The global input, proved in Lemmas 3.1 and 4.1 and Proposition 4.2 of the manuscript,
is not formalized. Theorem 1.1 is therefore formalized conditional on
`GlobalFibreBound`.

## Proof correspondence

| Manuscript argument | Lean source |
|---|---|
| Common real value off a countable set of radii | [FactoredFunction.lean](Erdos1117/FactoredFunction.lean), `maximum_points_common_value_off_countable` |
| Small-product fibre bound for the logarithmic derivative | [FactoredCoordinates.lean](Erdos1117/FactoredCoordinates.lean), `small_product_fiber_bound_of_order` |
| Maximum-point injection and the bound off a countable set | [FiberApplication.lean](Erdos1117/FiberApplication.lean), `maximum_bound_off_countable_of_global_fiber_bound` |
| Theorem 1.1, conditional on the global estimate | [Main.lean](Erdos1117/Main.lean), `theorem_1_1_of_entire` |
| Remark 5.1, sharpness of the factor 2 | [SharpExample.lean](Erdos1117/SharpExample.lean) |

## Use of generative AI

The proofs were generated with GPT-6 (Codex) and checked step by step by the author.
The Lean formalization was developed with OpenAI Codex (GPT-6); its coverage and
remaining hypothesis are listed above.
