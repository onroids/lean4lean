# Review and disposition of the earlier experiments

The retained results are the small reproducers and the conditional abstract
construction described in [README.md](README.md). The large executable-checker
proof prototype is not a completed soundness result. Several of its interfaces
need repair before extending that proof chain would be useful.

## What was reviewed

The main source snapshot is `a2413ca7416bfe242c45bb7c332353acf9a295cd`, based on
`8223d223ed98661882e95d9d6a7126df7097cd76`: 386 commits, 73 changed files,
51,476 inserted and 137 deleted lines. Every changed file is classified in
[legacy-inventory.json](legacy-inventory.json), with its content hash, disposition
and replacement where applicable. The original Git history and worktrees are
preserved locally. The curated branch does not carry the entire old prototype.

The review rebuilt the old theory, verification and probe targets on their pinned
Lean 4.33.1 toolchain; inspected the principal specifications and theorem
contracts; and traced theorem axioms in the changed modules. Separate import
sets are necessary because the old main and experimental confluence developments
declare overlapping names. A successful legacy build includes inherited
admissions and does not validate the truth of its assumptions. The old host-kernel
caveat is another reason to recheck the retained results on Lean 4.35.

Selected sources were then isolated from the old interface changes, rebuilt on
Lean 4.35.0, and tested with positive and negative controls. This is a review of
contracts, dependencies and reproducible behavior, not a claim that every line
of the 51,476-line prototype has received an independent correctness proof.
Exact checks and the legacy dependency summary are in
[validation.json](validation.json) and
[legacy-axioms-summary.json](legacy-axioms-summary.json).

## Abstract construction: what the theorem says

`IndSpec.addInductCore_WF4` preserves `VEnv.Ordered`, provided the input
environment is `Ordered`, the construction succeeds, and three predicates hold:

| Predicate | Obligation |
| --- | --- |
| `WFCore` | Block views exist; member and constructor types are well typed in their respective environments; fields satisfy typing, universe and positivity conditions; requested large elimination is justified. |
| `WFExact` | The syntactic telescope decomposition and reassembly operations agree exactly with the original types. Constructor obligations use the environment extended with the block's type constants. |
| `WFTele` | Five recursor telescope typing clauses hold in the environment containing both the type and constructor constants. |

`addInductCore_exists` supplies successful construction under additional name
freshness and distinctness conditions. The empty-datatype and recursive-datatype
witnesses prove all three predicates and successful ordered extension jointly.
The parameterized telescope and constructor probes establish narrower examples.
The old telescope probe inverted `TrExprS`, whose upstream definition depends
on an admitted projection relation. It is replaced by direct concrete typing
derivations; no translation-inversion result is asserted for the current baseline.

The proof does not derive all these predicates from executable checker acceptance.
`Ordered` also does not by itself establish consistency. The core imports only
the dependencies it needs and its transitive axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`. The whole-checker prototype's larger trust
assumptions are not imported into these results.

Two boundaries have executable controls: native Lean accepts definition-hidden
telescopes and equivalent, syntactically different result universes that
`mkViews` rejects. A historical `WFExact` environment defect was in our own
specification; its refutation and repaired witness are retained as regressions.

## Why the larger bridge was excluded

| Component | Review result |
| --- | --- |
| `InductScope.hwpo` | Quantifies over all contexts without the necessary environment restriction. A valid definition alias can unfold from an expression with no syntactic block occurrence to the block constant. The runtime counterexample does not claim a formal refutation of every `InductScope` premise together. |
| Draft `TrProj` | The index is unused and motive/minor are constrained only by typing. A standard-axiom proof now exhibits an `Ordered` environment and closed subject whose translation is not closed. This refutes the old closedness interface; it is not a native projection bug. |
| Expression model axioms | Known issues [#48](https://github.com/digama0/lean4lean/issues/48) and [#52](https://github.com/digama0/lean4lean/issues/52) reproduce. The inherited loose-bound-variable equation and metadata bound derive `False`; abstraction/instantiation also have concrete model mismatches. |
| Added traversal/annotation axioms | Some old bridges moved obligations into new trust assumptions. These extensions are recorded by the legacy audit and are unnecessary for the retained core. |
| Confluence | The old proof adds restrictive `pat_no_prop` and `pat_arg_not_fun` hypotheses. It also retains the root-pattern problem for lambda-abstracted equations. No general confluence claim is retained; compare [#55](https://github.com/digama0/lean4lean/pull/55), [#56](https://github.com/digama0/lean4lean/pull/56) and [#65](https://github.com/digama0/lean4lean/pull/65). |
| Large bridge and intermediate witnesses | Many local lemmas may be reusable, but the final contracts remain unresolved. The old List/MkRecInfos probes do not instantiate the complete soundness interface. They remain in the original snapshot. |
| Bounded fresh-universe fallback | This changes runtime behavior and is separate from the uniformity pass. It is excluded; [#62](https://github.com/digama0/lean4lean/pull/62) provides an upstream totalization proposal. |

The experimental pattern result has a precise target:
`Experimental/SExpr.lean` contains the global `SExpr.Params.extra_pat` axiom.
The quotient equation contradicts its root-only pattern requirement. A separate
test also refutes the corresponding experimental hypothesis in a quotient
environment. **PR #56 repairs a different, related field in the main confluence
interface; it does not propose the false global axiom.**

## Runtime changes and empirical evidence

The uniformity candidate is a separate wrapper, so the same raw declarations
exercise the complete baseline and candidate entry points. Beta- and let-erased
nonuniform occurrences are rejected by native Lean and the candidate, but
accepted by the pinned baseline. Valid variants, traversal controls and imported
native constructors supply positive controls. This concerns agreement with the
native acceptance policy, not a demonstrated native kernel soundness bug.

The replay repair compares Lean 4.35's full `ConstantInfo` equality. The old patch
at `18b8753f0b08eda3a2a2fa66b7fbdf4c5f78a269` compared only levels, type and
`value?`; the latter hides theorem and opaque bodies by default. New regressions
cover every constant kind, hidden bodies, safety and metadata. Collision checks
must run before the unsafe/partial filter as well as after dependency replay.
This uses Lean's structural equality, not a claim of byte-identical serialized
objects or definitional equality between different declarations.

The old 6,663/6,757 (98.6%) count was a syntactic scope screen, not the fraction
of declarations for which every theorem premise was constructed. Likewise,
997 duplicate hits were not established identical by the incomplete comparator.
Historical constructor-headed residue checks (345 probes over 94 blocks) remain
historical evidence. The old mathlib corpus was not rerun.

The native recursor-data checks in this branch include planted faults and fail
on mismatches. They establish consistency of the inspected native data, not
correctness of lean4lean's nested-inductive implementation. The separate
abstract differential test compares generated recursor types and iota rules
and checks their typing, with explicit counts for excluded cases.

A separate uncommitted runner experiment allowed native-kernel fallback after
lean4lean resource failures. It is preserved locally and excluded here: an
acceptance count from such a runner cannot establish independent acceptance by
lean4lean. No private operational notes were copied into this branch.

## Version and integration boundary

The base is upstream `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`. The toolchain
and Batteries are pinned to stable Lean 4.35.0. Compatibility edits are adapted
from Sebastian Ullrich's [#47](https://github.com/digama0/lean4lean/pull/47):
the new `Decidable` representation, removed native-reduction entry point and
associated imports/proof steps. The export runner from that PR is not included.

The default target is explicitly the research suite. The full upstream
`Lean4Lean.Verify` library is not a completed Lean 4.35 port. Its attempted build
fails in `Verify/Environment/Primitive/Condition.lean:2468`: `decide_tr_inv'`
still invokes an inversion lemma for the old `ite` expression, while the runtime
adapter now constructs `Decidable.decide`. See `validation.json` for the receipt.
Porting that proof is separate from validating this suite. The small candidate
patches need an agreed target baseline before becoming PRs.

The source mapping and contribution credits are in
[provenance.json](provenance.json). [ISSUE.md](ISSUE.md) is a coordination draft,
with immutable fork links supplied by `render_issue.py`. It offers the strongest
small pieces first and acknowledges the existing overlapping work.
