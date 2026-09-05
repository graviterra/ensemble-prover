# Commutation of iterated finite differences

Let A and B be arbitrary abelian groups, written additively. No continuity,
linearity, topology, or finiteness assumptions are imposed on a function f from
A to B. For h in A, define its finite difference D_h f by

    (D_h f)(x) = f(x + h) - f(x).

For a finite list H of increments in A, define I_H f recursively: the empty
list leaves f unchanged, and I_(h :: H) f = D_h (I_H f). Repeated increments
and the zero increment are permitted.

Prove that, for every such A, B, f, finite list H, increment k, and x in A,

    (D_k (I_H f))(x) = (I_H (D_k f))(x).

The intended argument first establishes that two finite difference operators
commute, expanding both sides and using commutativity in A and B. Then use
induction on H. The list order in the recursive definition must be preserved;
the theorem must not assume that f is additive. Build the missing definitions
and supporting commutation lemma as independently checked project components.
