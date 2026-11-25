# Search: obstruction to direct reduction modulo a fixed list of moduli

The project's L-alg-006 asks for a superpolynomial size lower bound for
integer syntactic R(lin) refutations of the bit pigeonhole family.
This note checks an obstruction to a proof method. It does not settle
that lower bound or SAT in P.

The 3-pigeon, 2-hole instance already supplies a counterexample to
coefficient-by-coefficient reduction of every valid integer proof.
From its six two-literal clauses one can derive the opposing units
`a = 0` and `a = 1` by ordinary resolution. The project's syntactic
integer rules allow the resulting units to be combined with multipliers
`N` and `-N`, obtaining the singleton line `0 = N`. Since `N ≠ 0`,
integer simplification removes the false equation and the line becomes
empty, as required for a refutation.

For any finite preset list of positive moduli, take `N` to be their
product. In each of those modular systems the selected equation reduces
to `0 = 0`. Dropping that equation is not simplification; it changes a
true singleton line into false. So no fixed finite palette makes direct
line-by-line reduction valid for every integer proof. In particular,
setting `N = 2` explains why an F2-only lower bound for resolution over
parities is not, by itself, a lower bound for the posted integer system.

This does not exclude normalization, changing the proof, or choosing a
modulus after inspecting the proof. It also does not show that refuting
the growing pigeonhole family can be done in polynomial size.

`SearchParityTrap.lean` builds a legal refutation using the repository's
`IsResLinQSynRefutation` and checks the finite-moduli result. It can be
run with `lake env lean /path/to/SearchParityTrap.lean` from the repository's
`lean` directory, using Lean 4.36.0 and the pinned Mathlib dependencies.
The result passed the unchanged project checker as a local test lemma, not as a desk assignment.

Sources:
- Search program: https://pequalnp.com/program#p_eq_np_search
- Syntax: https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/SearchQSyn.lean
- Comparator result (parities): https://arxiv.org/abs/2609.23015

Verification used upstream commit
`d0fa0f22c2f6e8449e57e762e996904dda6862cd`, with the proof checked as a
standalone research lemma. It is not an upstream submission.
