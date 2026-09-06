# Lean formalization

This project formalizes the local analytic and counting arguments of the
[current manuscript](paper/PROOF.tex), including the sharp example in Remark 5.1.
Theorem 1.1 is proved **conditional on `GlobalFibreBound`**. The global argument
establishing that hypothesis (Lemma 3.1, Lemma 4.1, and Proposition 4.2) remains
outside the formalization.

## Final statement and remaining hypothesis

[`GlobalFibreBound m k h`](Erdos1117/FiberApplication.lean) states precisely:
there is a countable set `S ⊆ (0, ∞)` such that, for every positive `r ∉ S` and
real `a > m`, the fibre of `(zw, A(z))` over `(r², a)` has `encard ≤ 2 * k`, where
`A = logarithmicDerivative (factoredFunction m h)` and the second coordinate
satisfies `reflected A w = a`. No bound at general complex products is assumed.

[`theorem_1_1_of_global`](Erdos1117/Main.lean) applies this hypothesis to `z^m h`.
`theorem_1_1_of_entire` starts directly from an entire `f ≠ 0` that is not of the
form `c * z^m`. It extracts `m = analyticOrderNatAt f 0`, an entire factor `h`
with `h(0) ≠ 0`, and

```lean
firstGap f hf hne = analyticOrderNatAt
  (fun z => entireFactor f hf hne z - entireFactor f hf hne 0) 0
```

It proves `0 < firstGap f hf hne`, a countable-exception bound for the actual
`maximumPoints f r`, and

```lean
∃ᶠ r in atTop, (maximumPoints f r).encard ≤ 2 * firstGap f hf hne
```

`encard` takes the value infinity on infinite sets, so each displayed finite
bound also proves finiteness. The top-level theorem assumes `GlobalFibreBound`
for the extracted factor and gap; it does not assume a factorization or local
coordinates from the caller.

## Maximum modulus points

`maximumPoints f r` is the set of points `z` with `‖z‖ = r` and
`‖f w‖ ≤ ‖f z‖` for every `w` on that circle. `circleSup` is the actual supremum of
these norms, and `logMaximum h x = log (circleSup h (exp x))`.

The main local theorem is:

```lean
maximum_points_common_value_off_countable (m : ℕ)
    (hh : Differentiable ℂ h) (h0 : h 0 ≠ 0)
    (hnc : ¬ ∃ c : ℂ, ∀ z, h z = c) :
  ∃ E : Set ℝ, E.Countable ∧ ∀ r : ℝ, 0 < r → r ∉ E →
    ∃ lam : ℝ, (m : ℝ) < lam ∧
      ∀ z ∈ maximumPoints (factoredFunction m h) r,
        logarithmicDerivative (factoredFunction m h) z = (lam : ℂ)
```

Here `factoredFunction m h z = z ^ m * h z` and
`logarithmicDerivative f z = z * deriv f z / f z`, used where `f z ≠ 0`.
[`regularLogarithmicDerivative m h`](Erdos1117/FactoredCoordinates.lean) is
`m + z * deriv h z / h z`; its value at zero is `m`.
`logarithmicDerivative_factored` proves equality with the raw quotient whenever
`z ≠ 0` and `h z ≠ 0`.
`factored_maximum_common_value` identifies `lam` with the derivative of
`m * x + logMaximum h x` at every differentiability point `x`.

Convexity is proved using mathlib's Hadamard three-lines theorem applied to `h ∘ exp`.
The strict inequality follows from the maximum modulus principle: the maximum modulus
of a nonconstant entire function strictly increases with radius. Its convex logarithm
therefore has positive derivative wherever differentiable. The manuscript now uses
this same convex secant-slope proof.

## Local counting and sharpness

`small_product_fiber_bound_of_coordinates` assumes injective local coordinates `χ, ψ`
on the punctured disc `0 < ‖z‖ ∧ ‖z‖ < η`, with `A z - m = χ z ^ k`
and `B z - m = ψ z ^ k` there.
For `k > 0`, `s ≠ 0`, and `‖s‖ < η ^ 2`, it proves that the **entire** set

```lean
productFiber A B s a = {p : ℂ × ℂ | p.1 * p.2 = s ∧ A p.1 = a ∧ B p.2 = a}
```

is finite and has at most `2 * k` elements.

[`exists_local_coordinate`](Erdos1117/LocalCoordinate.lean) constructs the coordinate
from `AnalyticAt ℂ F 0` and `analyticOrderAt F 0 = k > 0`: factor `F = z^k g`,
take a holomorphic kth root of the unit `g` using a logarithm near `g(z)/g(0) = 1`,
and apply the inverse function theorem to `χ(z) = z * root(g)(z)`.

[`logarithmicDerivative_order`](Erdos1117/FactoredCoordinates.lean) proves
`ord₀(zh′/h) = ord₀(h − h(0))`. Thus `small_product_fiber_bound_of_order` proves
the small-fibre estimate for the actual `A = zf′/f` and its reflection from the
Taylor order of `h`, with no assumed local coordinate. The punctured-disc
formulation avoids identifying the raw quotient's value at zero with its
holomorphic extension.

For `sharpFunction k z = exp (2 * z ^ k - z ^ (2 * k))`, the project proves the square
identity, the equality cases, and the exact counts of distinct maximum points:
`k` when `0 < r ^ k ≤ 1/2`, and `2 * k` when `r ^ k > 1/2`.
It also proves that the function is entire and that its logarithmic derivative equals
`2 * k * z ^ k * (1 - z ^ k)`, with the remaining factor nonzero at zero for `k > 0`.
The Taylor-series statement in the remark is not separately formalized.

## Global argument outside the project

The analytic correspondence, its irreducible components and normalizations, the
small-product sequence on every component (Lemma 3.1), properness, and the passage
from local counts to the total fibre bound (Proposition 4.2) remain unformalized.
Stoïlow, BRS, and Remmert are consequently not Lean dependencies of the local results.

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

## Build

Lean and mathlib are pinned to `v4.33.0`; exact dependencies are in
[lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
lake build
lake env lean Check.lean
lake env leanchecker Erdos1117
```

[GitHub Actions](https://github.com/FireflySentinel/erdos-1117/actions/workflows/lean.yml)
runs the unfinished-proof check, build, [axiom checks](Check.lean), and kernel replay.

The Lean formalization was developed with OpenAI Codex (GPT-6).
