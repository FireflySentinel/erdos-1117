# Verification and scope

The Lean development is partial. Its final theorems prove the maximum-point
bound from explicit global analytic hypotheses. Those hypotheses include
arguments of this manuscript that have not been formalized; they are not
statements of published results.

## Statements

[`theorem_1_1_of_entire_component_data`](Erdos1117/FibreComponents.lean) starts with a nonzero,
non-monomial entire function, extracts its zero order and first Taylor gap `k`,
and proves that the maximum-point set has cardinality at most `2k` outside a
countable set of positive radii. It assumes the two component properties below
for the logarithmic derivative of `f` itself.
[`checks/Statement.lean`](checks/Statement.lean) expands those properties, the
regular image and the maximum-point set, with the bound expressed as `∃ k > 0`.

The entry point and its factored version `theorem_1_1_of_component_data` assume
a countable exceptional set `T` and the following two properties of the regular
image of the product/common-value map:

* `FibreDegreeConstancy`: the cardinality of the **whole fibre** is locally constant.
* `SmallProductsOnComponents`: every connected component meets arbitrarily small
  nonzero products.

The local `2k` bound, its propagation over each connected component, and the
projection of `T` to a countable exceptional set of radii are proved. Thus this
theorem accounts for multiple source components over the same image component.

## Properness and finite fibres

[`ProperCorrespondence.lean`](Erdos1117/ProperCorrespondence.lean) proves the
properness and finite-fibre assertions of Lemma 4.1 in graph coordinates:

\[
 p(z)=\lambda q(z),\qquad P(w)=\lambda Q(w),\qquad
 (z,w,\lambda)\longmapsto(zw,\lambda).
\]

The hypotheses include the numerator/denominator data, continuity (entireness
where the isolated-zero argument is used), nonvanishing denominators at zero,
and common value `m` at zero. The target excludes `zw = 0` and `λ = m`.
`correspondenceMap_isProper` uses Mathlib's `IsProperMap`;
`correspondenceMap_fiber_finite` proves finiteness of every fibre.
`correspondenceMap_range_isClosed` proves that the image is closed in the base.
`quotient_equation_iff` identifies the equations with the ordinary quotient
equations when numerator and denominator have no common zero.
The global construction of such a representation for the meromorphic logarithmic
derivative is not part of this module.

[`factored_productFiber_finite`](Erdos1117/FactoredCorrespondence.lean) proves
finiteness directly for the actual logarithmic derivative of `z^m h(z)` when
`s ≠ 0` and `λ ∉ {0,m}`. It uses `p = m h + z h'`, `q = h`: the resulting
graph equations contain the actual fibre, which suffices for finiteness even
when numerator and denominator have common zeros. This application requires
only entireness of `h` and `h(0) ≠ 0`.

## Remaining analytic applications

| Source used in the manuscript | Connection still to be formalized |
|---|---|
| Stoïlow's continuation theorem, in the formulation of [Eremenko, *Singularities of implicit functions* (2015)](https://www.math.purdue.edu/~eremenko/dvi/gross2.pdf); [Bergweiler–Rippon–Stallard (2008), Theorem 2.1](https://arxiv.org/abs/0704.2712) | Lemma 3.1: every irreducible source component has arbitrarily small products |
| [Demailly, Chapter II, Theorem 8.8, p. 118](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf) (Remmert) and Theorem 7.12, pp. 114–115 (normalization), followed by covering theory | Construction of the regular image and exceptional set; local constancy of the total fibre cardinality |
| Lemma 3.1 and the connectedness of a normalized curve after deleting the exceptional points | `SmallProductsOnComponents` for the actual image |

The two component hypotheses express the required outputs of these arguments.
The [FC bridge](checks/FormalConjecturesBridge.lean) takes their universal
statements as parameters: the first supplies `T`, its countability, local
finiteness relative to the image, and degree constancy; the second supplies
small products for that same `T`. It calls the entire-function entry point.

The FC statement keeps the second question open and records the conditional
implications as variants, with both assumed claims stated in the problem file. This does not meet the distinct
requirement of a solution conditional only on published inputs in the
[teorth database's contribution rules](https://github.com/teorth/erdosproblems/blob/main/CONTRIBUTING.md).

## Reproduction

The toolchain and dependency revisions are pinned in `lean-toolchain` and
`lake-manifest.json`. From the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos1117
```

`lake test` builds the expanded statement and the axiom guards in `checks/`.
The guards require `propext`, `Classical.choice`, and `Quot.sound`; theorem
parameters remain assumptions regardless of this axiom list. The
[workflow](.github/workflows/lean.yml) also replays the project declarations
through the kernel. Tag `v0.3.0` records this partial formalization.
