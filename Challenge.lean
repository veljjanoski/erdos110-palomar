module

public import Mathlib

/-!
# Erdős Problem 110: the de Bruijn–Erdős variant

A solved statement about Erdős Problem 110
([erdosproblems.com/110](https://www.erdosproblems.com/110)). The statement is copied verbatim
from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Apache-2.0),
file `FormalConjectures/ErdosProblems/110.lean` at commit
`a64e959c32c270df4dd0d96d2027481f15750534`, with the same name. It uses only Mathlib definitions.

*References:*
- [dBEr51] de Bruijn, N. G. and Erdős, P., *A colour problem for infinite graphs and a problem in
  the theory of relations*. Indag. Math. (1951), 369--373.
-/

@[expose] public section

open Filter

namespace Erdos110

/--
A theorem of de Bruijn and Erdős [dBEr51] implies that, if $G$ has infinite chromatic number,
then $G$ has a finite subgraph of chromatic number $n$ for every $n\geq 1$.

Infinite chromatic number is `G.chromaticNumber = ⊤`.
-/
theorem erdos_110.variants.de_bruijn_erdos {V : Type*} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ H.coe.chromaticNumber = (n : ℕ∞) := by
  sorry

end Erdos110
