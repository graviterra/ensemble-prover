# Weighted binary cost trees

Construct the objects below and prove the final BumpMirrorRoot identity for all
natural numbers and all finite trees. The supporting identities are separate
mathematical tasks whose proofs should be reused by the final result.

## Definitions

A CostTree is a finite inductive tree. A leaf contains a natural-number weight;
a fork contains a left CostTree and a right CostTree. There are no other cases.

The cost of a leaf of weight n is n, and the cost of a fork is the sum of its
children's costs. The number of leaves of a leaf is 1; the number of leaves of
a fork is the sum of the two children's numbers of leaves.

The mirror of a leaf is that same leaf. To mirror a fork, recursively mirror
its children and exchange their positions. For a natural number k, bump k adds
k to every leaf weight and preserves the tree's branching structure. Thus the
weight n becomes n + k; bump acts recursively on both children of a fork.

## Archival appendix

This space can contain unrelated archival material. Its contents impose no
additional mathematical assumptions. The regression test inserts more than
two mebibytes here to exercise exact indexed retrieval of the later claims.

<!-- TEST_APPENDIX -->

## BumpCostIdentity

For every natural number k and every CostTree t,

    cost (bump k t) = cost t + leaves t * k.

Proof plan:
Fix k and use structural induction on t. At a leaf, unfold bump, cost, and
leaves and simplify the multiplication by 1. At a fork, unfold the recursive
definitions, apply both induction hypotheses, distribute multiplication over
the sum of the leaf counts, and rearrange natural-number additions.

## MirrorCostIdentity

For every CostTree t,

    cost (mirror t) = cost t.

Proof plan:
Use structural induction on t. The leaf case is reflexive. At a fork, unfold
mirror and cost, apply both induction hypotheses, and commute the two costs.

## MirrorLeavesIdentity

For every CostTree t,

    leaves (mirror t) = leaves t.

Proof plan:
Use structural induction on t. The leaf case is reflexive. At a fork, unfold
mirror and leaves, apply both induction hypotheses, and commute the counts.

## BumpMirrorRoot

For every natural number k and every CostTree t,

    cost (bump k (mirror t)) = cost t + leaves t * k.

The quantifiers include k = 0 and trees consisting of a single leaf. No bound
on weights, tree size, depth, or k is assumed.

Proof plan:
Introduce the arbitrary k and t. Rewrite the left side using BumpCostIdentity
at mirror t. Rewrite the resulting cost and leaf count using MirrorCostIdentity
and MirrorLeavesIdentity. The resulting equality is reflexive.
