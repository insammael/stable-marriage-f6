# Stable Marriage F6

This repository accompanies *Small Rotation Blocks and the Order-Six Stable
Marriage Problem*.

Zenodo preprint DOI: [10.5281/zenodo.22860585](https://doi.org/10.5281/zenodo.22860585).

The manuscript proves the order-six result by human mathematics. The Lean
development verifies important components, including the following finite-
poset theorem, which is the only result advertised in the Palomar files:

> If `P` is a finite poset with `|P| ≤ 15`, `width(P) ≤ 3`, and CI2, then
> `P` has at most `48` antichains.

The proof reused by `palomar/Solution.lean` is
`F6ConvexWindow.totalAntichains_le_48`.

The Lean project does **not** formalize the full stable-marriage theorem
`f(6) = 48` end to end. In particular, the classical rotation semantics, the
stable-matching/downset correspondence, and the human semantic bridge from
rotations to the abstract token model remain outside the Lean development.

## Contents

- `paper/`: public manuscript and supplement, source and PDF.
- `lean/`: audited formal development and provenance notes.
- `palomar/`: the small Challenge/Solution statement surface and metadata.
- `verification/`: audit summaries, reproducible checkers, logs, and hashes.

## Reproduction

From the repository root:

```sh
lake build
lake env lean palomar/AxiomAudit.lean
python3 verification/certificates/check_ds3_pstar.py
```

The candidate builds successfully with Lean 4.33.1 and Mathlib v4.33.1, and
the fresh axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. One proof-syntax-only cardinality-cast normalization was needed
for Mathlib 4.33.1; the exact hunk is documented in
`verification/LEAN_COMPATIBILITY_DIFF.txt`. The public theorem statements are
identical to v07.

`palomar/Challenge.lean` deliberately contains one `sorry`, as required for
the Challenge/Solution separation. The proof development and Solution are
required to be admission-free.

The current Palomar Comparator/NanoDa preflight is Linux-oriented. Under the
current Palomar policy, authoritative Comparator, Lean kernel, and mandatory
NanoDa replay runs remotely on the immutable public GitHub commit. Those
checks were therefore not run locally and are recorded as deferred rather
than failed; the configuration and metadata schemas were validated locally.

## Priority and provenance

The manuscript retains its cautious statement concerning Roman Parks and the
Biola University project announcement and makes no priority claim. It contains
a concise generative-AI tools declaration; policy-specific automation
provenance remains in the relevant metadata and audit files.

## License

Repository-authored code and metadata are released under Apache-2.0; see
`LICENSE`. Third-party material retains the provenance and terms recorded in
`lean/third_party/`.
