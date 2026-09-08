# Erdős Problem #1117: the second question answered in the negative

Lean 4 formalization for [Erdős Problem #1117](https://www.erdosproblems.com/1117):
no non-monomial entire function has $\nu_f(r)\to\infty$.
[`theorem_1_1_of_entire_component_data`](Erdos1117/FibreComponents.lean) derives
`(maximumPoints f r).encard ≤ 2 * k` outside a countable set of radii, from two
component properties that remain hypotheses of the manuscript's analytic argument.
[VERIFICATION.md](VERIFICATION.md) states them and their literature sources.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos1117
```

## Proof correspondence

| Manuscript argument | Lean source |
|---|---|
| Common real value off a countable set of radii | [FactoredFunction.lean](Erdos1117/FactoredFunction.lean), `maximum_points_common_value_off_countable` |
| Small-product fibre bound for the logarithmic derivative | [FactoredCoordinates.lean](Erdos1117/FactoredCoordinates.lean), `small_product_fiber_bound_of_order` |
| Lemma 4.1, in numerator-denominator graph coordinates | [ProperCorrespondence.lean](Erdos1117/ProperCorrespondence.lean), `correspondenceMap_isProper`, `correspondenceMap_fiber_finite` |
| Finite fibres for the actual logarithmic derivative | [FactoredCorrespondence.lean](Erdos1117/FactoredCorrespondence.lean), `factored_productFiber_finite` |
| Proposition 4.2, propagation of the local bound across regular components | [FibreComponents.lean](Erdos1117/FibreComponents.lean), `globalFibreBound_of_component_data` |
| Maximum-point injection and the bound off a countable set | [FiberApplication.lean](Erdos1117/FiberApplication.lean), `maximum_bound_off_countable_of_global_fiber_bound` |
| Theorem 1.1, starting from the entire function | [FibreComponents.lean](Erdos1117/FibreComponents.lean), `theorem_1_1_of_entire_component_data` |
| Remark 5.1, sharpness of the factor 2 | [SharpExample.lean](Erdos1117/SharpExample.lean) |

[Statement.lean](checks/Statement.lean) expands both component inputs and the conclusion;
[FormalConjecturesBridge.lean](checks/FormalConjecturesBridge.lean) derives the negative
answer from the two named analytic claims.

## Use of generative AI

GPT-6 Astra proposed the argument and drafted the manuscript.
The Lean formalization was generated with OpenAI Codex (GPT-6).
The author checked the arguments step by step and is responsible for the content.
