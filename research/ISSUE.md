# Reviewed inductive experiments: small reproducers and reusable abstract proofs

I have cleaned up an earlier experiment on inductive declarations into a
[research branch](__FORK_URL__/blob/__REVISION__/research/README.md).
It is based on `67f63b0`, with Lean 4.35.0 and runtime compatibility changes
from #47. One command builds the experiment suite and checks its axiom
dependencies. The full `Verify` target is outside this migration's scope.

The potentially useful pieces are:

1. **Constructor uniformity precheck.**
   [Raw declarations](__FORK_URL__/blob/__REVISION__/Lean4Lean/Research/UniformityTests.lean)
   show lean4lean accepting nonuniform occurrences erased by beta reduction
   or a let, while native Lean rejects them. A small candidate precheck,
   based on Lean 4.35's traversal, agrees with the native controls.
2. **Experimental pattern axiom counterexample.**
   [A short proof](__FORK_URL__/blob/__REVISION__/Lean4Lean/Research/PatternRefutation.lean)
   derives `False` from `SExpr.Params.extra_pat`, `propext`, and `Quot.sound`:
   the quotient equation has a lambda-headed lhs, which `MatchesS` cannot
   match. This concerns the global axiom in `Experimental/SExpr.lean`.
   #56 repairs the related main-interface field; it does not propose this
   false axiom.
3. **Abstract inductive construction.**
   [The isolated model and proofs](__FORK_URL__/tree/__REVISION__/Lean4Lean/Research/Inductive)
   establish preservation of `Ordered` under explicit `WFCore`, `WFExact`,
   and `WFTele` assumptions, using only standard axioms. There are existence,
   nonvacuity, differential and negative-scope checks. This is not a completed
   executable-checker soundness proof.
4. **Duplicate replay repair.**
   [The patch and regressions](__FORK_URL__/blob/__REVISION__/Lean4Lean/Research/ReplayTests.lean)
   reuse matching existing declarations after comparing all `ConstantInfo`
   fields, and reject changed proof bodies, kinds, safety and metadata.

The [review record](__FORK_URL__/blob/__REVISION__/research/REVIEW.md) explains
what was excluded from the larger prototype and corrects its earlier coverage
claims. Known model-axiom problems are attributed to #48/#52. I have not
rerun the old mathlib corpus or found a native kernel soundness bug.

I am aware of the overlapping work in #43, #53/#54, #55/#56, #62, #64 and #65.
Which of these pieces would help that work? In particular, would a small PR
for the uniformity pass or duplicate replay behavior be useful, and on which
baseline?
