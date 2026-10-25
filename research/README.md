# Reviewed lean4lean experiments

This branch collects reproducible findings and an isolated model of inductive
declarations. Start with the small reproducers below; the abstract construction
is optional reading. The earlier whole-checker prototype is preserved in its
original branch and classified in [REVIEW.md](REVIEW.md).

The baseline is upstream `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, with Lean
**4.35.0** and pinned Batteries. Runtime compatibility edits come from
[PR #47](https://github.com/digama0/lean4lean/pull/47). The default build checks
this research suite. **It does not certify or finish porting upstream's full
`Lean4Lean.Verify` target.** See [validation.json](validation.json) for exact
checks, revisions, counts, and limitations.

## Reproduce

```sh
bash research/check.sh
```

This builds every module under `Lean4Lean/Research`, then audits transitive
axiom dependencies. Runtime assertions execute during module compilation;
Lake can reuse a successful result when its inputs have not changed. Failed
assertions and unexpected axioms fail the command. No mathlib checkout is needed.

The recorded run audits **750 declarations**. Only three explicitly named
contradiction proofs use disputed axioms; the other 747 use only standard
axioms. See the [declaration record](axioms.json) and
[test output](validation-events.txt).

## Small findings

| Read | What it establishes |
| --- | --- |
| [UniformityTests.lean](../Lean4Lean/Research/UniformityTests.lean) | The complete lean4lean entry point accepts a beta- or let-erased nonuniform occurrence that Lean 4.35 rejects. The [candidate precheck](../Lean4Lean/Research/Uniformity.lean) agrees with native Lean on the fixtures and accepts the imported native constructor corpus. |
| [ReplayTests.lean](../Lean4Lean/Research/ReplayTests.lean) and the [Replay change](../Lean4Lean/Replay.lean) | Identical existing declarations can be reused. Conflicts in bodies, kinds, types, universes, safety and metadata are rejected. Equality uses Lean 4.35's full `ConstantInfo` `BEq`, not the old `value?` comparison. |
| [PatternRefutation.lean](../Lean4Lean/Research/PatternRefutation.lean) | The global experimental axiom `SExpr.Params.extra_pat` derives `False`: a lambda-headed quotient equation cannot satisfy the root-only pattern relation. The dependency list contains that axiom, `propext`, and `Quot.sound`. |

The pattern result concerns `Experimental/SExpr.lean`. **PR #56 repairs a
related field in the main confluence interface; it does not introduce this
false axiom.** The global experimental axiom remains in this pinned baseline.
No native Lean kernel unsoundness is claimed.

## Abstract construction

Read [Spec](../Lean4Lean/Research/Inductive/Spec.lean), then the final theorem
`IndSpec.addInductCore_WF4` in
[Transport](../Lean4Lean/Research/Inductive/Transport.lean). It proves
preservation of `VEnv.Ordered` under **three explicit predicates**:
`WFCore`, `WFExact`, and `WFTele`, assuming the construction succeeds.
[Exists](../Lean4Lean/Research/Inductive/Exists.lean) supplies existence under
freshness and distinct-name conditions;
[WF](../Lean4Lean/Research/Inductive/WF.lean) contains the recursor and iota-rule
typing proofs. Their transitive dependencies are checked against only
`propext`, `Classical.choice`, and `Quot.sound`.

This model is separate from upstream `VInductDecl.WF` and `VEnv.addInduct`.
It requires syntactic telescope and reassembly conditions, and it does not
establish consistency or correspondence with every accepted declaration.

- [EmptyBlockWitness](../Lean4Lean/Research/EmptyBlockWitness.lean) jointly
  witnesses the predicates and successful ordered extension for an empty
  datatype in both elimination modes.
- [RecursiveBlockWitness](../Lean4Lean/Research/RecursiveBlockWitness.lean)
  jointly witnesses the predicates and successful ordered extension for a
  Nat-shaped datatype with two constructors, a recursive field and large elimination.
- [TelescopeWitness](../Lean4Lean/Research/TelescopeWitness.lean) and
  [CtorIsType](../Lean4Lean/Research/CtorIsType.lean) exercise parameterized,
  indexed and recursive typing conditions. They do not witness every premise
  for arbitrary declarations.
- [InductiveDifferential](../Lean4Lean/Research/InductiveDifferential.lean)
  compares generated recursor types and iota rules with native data and checks
  their typing. Nested and large-literal cases are counted separately.
- [SpecLimits](../Lean4Lean/Research/SpecLimits.lean) shows two native-accepted
  cases the model rejects: equivalent but syntactically different universes,
  and a definition-hidden telescope.
- [ConstructorEnvironment](../Lean4Lean/Research/ConstructorEnvironment.lean)
  records a repaired defect in **our** `WFExact` predicate.

## Results we withdrew

[ProjectionCounterexample](../Lean4Lean/Research/ProjectionCounterexample.lean)
refutes the claimed closedness property of our old `TrProj` definition, even
in an `Ordered` environment. The rejected definition is local to that test.
[ScopeCounterexample](../Lean4Lean/Research/ScopeCounterexample.lean) exposes
the missing environment restriction in the old `InductScope.hwpo` premise.
[InheritedModelCounterexample](../Lean4Lean/Research/InheritedModelCounterexample.lean)
reproduces already-reported issues #48 and #52; these are not new discoveries.

The old “98.6% coverage” figure was a syntactic screen, not verified coverage.
The old duplicate scan did not compare complete contents. Neither claim is
carried forward. [KernelRecursorChecks](../Lean4Lean/Research/KernelRecursorChecks.lean)
checks native recursor data with planted-fault controls; it is not a validation
of lean4lean's nested-inductive implementation.

## Proposed issue

[ISSUE.md](ISSUE.md) is the concise coordination draft. After choosing a fork
and committing the final branch, render immutable links locally:

```sh
python3 research/render_issue.py OWNER/REPOSITORY
```

The renderer only prints text. It does not create a fork, push, or submit anything.
