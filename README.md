# A negative answer to a question of Erdős on maximum modulus points

Preprint answering the second question of
[Erdős Problem #1117](https://www.erdosproblems.com/1117) in the negative: no non-monomial
entire function has $\nu_f(r)\to\infty$.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos1117
```

## Exact statement

[`theorem_1_1_of_entire`](Erdos1117/Main.lean) starts with a nonzero,
non-monomial entire function and extracts its zero order and Taylor gap $k$.
Assuming [`GlobalFibreBound`](Erdos1117/FiberApplication.lean), it proves
`(maximumPoints f r).encard ≤ 2 * k` outside a countable set of positive radii
and at arbitrarily large radii. The use of `encard` includes finiteness in the bound.

[`theorem_1_1_of_component_data`](Erdos1117/FibreComponents.lean) derives the same
conclusion from constancy of the total fibre size and small products on each
regular image component. These two properties remain assumptions from the
manuscript's analytic argument. Properness is proved for a supplied
numerator-denominator representation; finiteness of the relevant fibres is
also proved directly for the actual logarithmic derivative.

This is a partial formalization. [VERIFICATION.md](VERIFICATION.md) gives the
remaining dependencies and their literature sources;
[Statement.lean](checks/Statement.lean) expands the global input and the conclusion.

## Proof correspondence

| Manuscript argument | Lean source |
|---|---|
| Common real value off a countable set of radii | [FactoredFunction.lean](Erdos1117/FactoredFunction.lean), `maximum_points_common_value_off_countable` |
| Small-product fibre bound for the logarithmic derivative | [FactoredCoordinates.lean](Erdos1117/FactoredCoordinates.lean), `small_product_fiber_bound_of_order` |
| Lemma 4.1, in numerator-denominator graph coordinates | [ProperCorrespondence.lean](Erdos1117/ProperCorrespondence.lean), `correspondenceMap_isProper`, `correspondenceMap_fiber_finite` |
| Finite fibres for the actual logarithmic derivative | [FactoredCorrespondence.lean](Erdos1117/FactoredCorrespondence.lean), `factored_productFiber_finite` |
| Proposition 4.2, propagation of the local bound across regular components | [FibreComponents.lean](Erdos1117/FibreComponents.lean), `globalFibreBound_of_component_data` |
| Maximum-point injection and the bound off a countable set | [FiberApplication.lean](Erdos1117/FiberApplication.lean), `maximum_bound_off_countable_of_global_fiber_bound` |
| Theorem 1.1, conditional on the global estimate | [Main.lean](Erdos1117/Main.lean), `theorem_1_1_of_entire` |
| Remark 5.1, sharpness of the factor 2 | [SharpExample.lean](Erdos1117/SharpExample.lean) |

## Use of generative AI

The proofs were generated with GPT-6 (Codex) and checked step by step by the author.
The Lean formalization was developed with OpenAI Codex (GPT-6); its coverage and
remaining hypothesis are listed above.
