# Erdős Problem #1117: a bound for the number of maximum modulus points

Preprint answering the second question of
[Erdős Problem #1117](https://www.erdosproblems.com/1117) in the negative: no non-monomial
entire function has $\nu_f(r)\to\infty$.

[Preprint PDF](paper/PROOF.pdf) · [LaTeX source](paper/PROOF.tex)

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

All theorem names below are in the `Erdos1117` namespace.

| Manuscript argument | Lean theorem | Module |
|---|---|---|
| Angular and logarithmic radial differentiation | `angular_derivative`, `radial_derivative` | [Derivatives](Erdos1117/Derivatives.lean) |
| Equality of derivatives at a contact point | `derivative_at_contact`, `maximum_point_common_value` | [MaximumPoints](Erdos1117/MaximumPoints.lean) |
| Hadamard convexity and strict growth of maximum modulus | `logMaximum_convex`, `logMaximum_derivative_pos` | [MaximumModulus](Erdos1117/MaximumModulus.lean) |
| Common real value greater than `m` | `factored_maximum_common_value`, `maximum_points_common_value_off_countable` | [FactoredFunction](Erdos1117/FactoredFunction.lean) |
| Countably many nondifferentiability points | `convex_countable_nondifferentiable` | [Convexity](Erdos1117/Convexity.lean) |
| Exceptional radii and arbitrarily large radii outside them | `exists_large_nonexceptional`, `frequently_bounded_of_countable_exceptions` | [Exceptions](Erdos1117/Exceptions.lean) |
| Entire factorization and positive Taylor gap | `exists_entire_factor`, `firstGap_pos` | [EntireFactor](Erdos1117/EntireFactor.lean) |
| Local power coordinate from the order of a zero | `exists_local_coordinate` | [LocalCoordinate](Erdos1117/LocalCoordinate.lean) |
| At most `k` local roots at either end | `coordinate_fiber_bound` | [LocalRoots](Erdos1117/LocalRoots.lean) |
| Small-product fibre bound | `small_product_fiber_bound_of_coordinates` | [SmallFiber](Erdos1117/SmallFiber.lean) |
| Local estimate for the actual logarithmic derivative | `small_product_fiber_bound_of_order` | [FactoredCoordinates](Erdos1117/FactoredCoordinates.lean) |
| Maximum-point injection and conditional final bound | `maximum_points_bound_of_fiber`, `maximum_bound_off_countable_of_global_fiber_bound` | [FiberApplication](Erdos1117/FiberApplication.lean) |
| Theorem 1.1 from the original entire function, conditional on the global estimate | `theorem_1_1_of_entire` | [Main](Erdos1117/Main.lean) |
| Remark 5.1 | `sharp_maximum_card_small`, `sharp_maximum_card_large`, `sharp_logarithmicDerivative` | [SharpExample](Erdos1117/SharpExample.lean) |

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition and
did not contribute to the mathematical arguments. The author reviewed the final
manuscript and takes full responsibility for its content.

The Lean formalization was developed with OpenAI Codex (GPT-6).
