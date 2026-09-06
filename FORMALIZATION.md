# Lean formalization

This project formalizes the local arguments in Sections 4–5 and the sharp example in
Remark 5.1. Lemma 3.1 and Proposition 4.2 are not proved here, so this is a partial
formalization of Theorem 1.1.

The manuscript reference is [commit 2dcd748](https://github.com/FireflySentinel/erdos-1117/tree/2dcd748882807de03850a864e174e8a393d0389a).
The LaTeX and PDF are unchanged by the addition of Lean.

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
`logarithmicDerivative f z = z * deriv f z / f z`.
`factored_maximum_common_value` identifies `lam` with the derivative of
`m * x + logMaximum h x` at every differentiability point `x`.

Convexity is proved using mathlib's Hadamard three-lines theorem applied to `h ∘ exp`.
The strict inequality follows from the maximum modulus principle: the maximum modulus
of a nonconstant entire function strictly increases with radius. Its convex logarithm
therefore has positive derivative wherever differentiable. This avoids the manuscript's
separate limit argument at minus infinity.

## Local counting and sharpness

`small_product_fiber_bound_of_coordinates` assumes injective local coordinates `χ, ψ`
on `‖z‖ < η`, with `A z - m = χ z ^ k` and `B z - m = ψ z ^ k` there.
For `k > 0`, `s ≠ 0`, and `‖s‖ < η ^ 2`, it proves that the **entire** set

```lean
productFiber A B s a = {p : ℂ × ℂ | p.1 * p.2 = s ∧ A p.1 = a ∧ B p.2 = a}
```

is finite and has at most `2 * k` elements. The two local root bounds are proved from
the coordinate equations. Existence of these local coordinates from the order of
vanishing is not formalized.

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

`maximum_bound_off_countable_of_global_fiber_bound` records the final application
with Proposition 4.2's total fibre estimate on the relevant real range `lam > m`
as an explicit hypothesis. Positive common values exclude zeros of `f` in either
coordinate. The application combines
that estimate with the proved common-value theorem and the countable exceptional set.
This conditional theorem does not supply the missing global estimate.

## Proof correspondence

All theorem names below are in the `Erdos1117` namespace.

| Manuscript argument | Lean theorem | Module |
|---|---|---|
| Angular and logarithmic radial differentiation | `angular_derivative`, `radial_derivative` | [Derivatives](Erdos1117/Derivatives.lean) |
| Equality of derivatives at a contact point | `derivative_at_contact`, `maximum_point_common_value` | [MaximumPoints](Erdos1117/MaximumPoints.lean) |
| Hadamard convexity and strict growth of maximum modulus | `logMaximum_convex`, `logMaximum_derivative_pos` | [MaximumModulus](Erdos1117/MaximumModulus.lean) |
| Common real value greater than `m` | `factored_maximum_common_value`, `maximum_points_common_value_off_countable` | [FactoredFunction](Erdos1117/FactoredFunction.lean) |
| Countably many nondifferentiability points | `convex_countable_nondifferentiable` | [Convexity](Erdos1117/Convexity.lean) |
| Exceptional radii and arbitrarily large radii outside them | `exceptionalRadii_countable`, `exists_large_nonexceptional`, `not_tendsto_atTop_of_countable_exceptions` | [Exceptions](Erdos1117/Exceptions.lean) |
| At most `k` local roots at either end | `coordinate_fiber_bound` | [LocalRoots](Erdos1117/LocalRoots.lean) |
| Small-product fibre bound | `small_product_fiber_bound_of_coordinates` | [SmallFiber](Erdos1117/SmallFiber.lean) |
| Maximum-point injection and conditional final bound | `maximum_points_bound_of_fiber`, `maximum_bound_off_countable_of_global_fiber_bound` | [FiberApplication](Erdos1117/FiberApplication.lean) |
| Remark 5.1 | `sharp_maximum_card_small`, `sharp_maximum_card_large`, `sharp_logarithmicDerivative` | [SharpExample](Erdos1117/SharpExample.lean) |

## Build

Lean and mathlib are pinned to `v4.33.0-rc2`; exact dependencies are in
[lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
lake build
lake env lean Check.lean
lake env leanchecker Erdos1117
```

[GitHub Actions](https://github.com/FireflySentinel/erdos-1117/actions/workflows/lean.yml)
runs the build, [axiom checks](Check.lean), and kernel replay.

The Lean formalization was developed with OpenAI Codex (GPT-6).
