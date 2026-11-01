# Erdős Problem 110: finite subgraphs of every chromatic number

[![CI](https://github.com/veljjanoski/erdos110-palomar/actions/workflows/ci.yml/badge.svg)](https://github.com/veljjanoski/erdos110-palomar/actions/workflows/ci.yml)

A Lean 4 proof of a solved statement about
[Erdős Problem 110](https://www.erdosproblems.com/110), prepared for the
[Palomar](https://palomar-registry.org/) registry (submission form:
<https://submit.palomar-registry.org/>).

The proved statement is a consequence of the de Bruijn–Erdős theorem (1951):

- `Erdos110.erdos_110.variants.de_bruijn_erdos`: if a graph $G$ has infinite chromatic number,
  then for every $n \geq 1$ it has a finite subgraph with chromatic number exactly $n$.

The statement in `Challenge.lean` is copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/110.lean` at commit
`a64e959c32c270df4dd0d96d2027481f15750534`), where it is stated with `sorry`. It uses only
Mathlib definitions.

The proof in `Solution.lean` uses Mathlib's compactness theorem for graph homomorphisms to find a
finite subgraph that is not $(n-1)$-colourable, and a minimal such subgraph has chromatic
number exactly $n$.

## Repository map

- `Challenge.lean`: the statement (with `sorry`) a reader audits.
- `Solution.lean`: the same declaration with a proof.
- `comparator.json`: the declarations `lake comparator` checks.
- `formalization.yaml`: provenance, authorship, automation and review metadata.
- `scripts/`, `test/`, `Gemfile*` and `.github/workflows/ci.yml` come from
  [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate).

Build with `lake exe cache get && lake build`; check with `scripts/verify-comparator.sh` (Linux,
needs `bwrap`).

## Licence

Apache License 2.0, see `LICENSE`. The statement copied from formal-conjectures is also under
Apache-2.0.
