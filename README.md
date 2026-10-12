# Focusing for infinitary action logic with multiplexing

Lean 4 formalization associated with Tikhon Pshenitsyn's dissertation, theorem
`theorem:focusing`. The source is in **FocusingComplete.lean**. No Mathlib or
external Lean libraries are required; only Lean's bundled `Std` is imported.

## Statement

The mathematical result is the equivalence between derivability in the ordinary
infinitary action calculus with multiplexing, arbitrary cut, and a simple set of
hypotheses, and derivability of the corresponding initial focused sequent.
A simple set of hypotheses consists of sequents with empty antecedent, `⇒ A`.

The Lean declaration is:

```lean
theorem Focusing.focusing {H : Focusing.Theory} {Γ : Focusing.Context}
    {A : Focusing.Formula} :
    Focusing.Ordinary H Γ A ↔ Focusing.Focused H (Focusing.root Γ A)
```

`Focusing.focusing_complete` proves the ordinary-to-focused direction without
assuming any unproved admissibility or normalization lemma. `Ordinary` includes
arbitrary cut and hypotheses. Cut normalization is proved within the source.

## Correspondence with the dissertation

| Mathematical notation | Lean representation |
| --- | --- |
| Propositional variables | `Formula.atom p`, with `p : Nat` |
| 0, 1 | `Formula.zero`, `Formula.one` |
| Product A · B | `Formula.tensor A B` |
| Left division A \\ B | `Formula.ldiv A B` |
| Right division B / A | `Formula.rdiv B A` |
| Additive conjunction and disjunction | `Formula.conj`, `Formula.disj` |
| Iteration A* | `Formula.star A` |
| Multiplexing !A | `Formula.bang A` |
| Finite ordered antecedent Γ | `Context := List Formula` |
| Simple hypothesis set H | `Theory := Formula → Prop`; `H A` means `(⇒ A) ∈ H` |
| Ordinary derivability with cut and hypotheses | `Ordinary H Γ A` |
| Initial sequent · ↑ Γ ⇒ A ↑ · | `root Γ A := Judgment.up [] Γ A Side.active` |
| Focused derivability | `Focused H j` |

Contexts are ordered lists; no exchange rule is added. Empty contexts are allowed.
The left iteration rule is genuinely infinitary: its premise is a function giving
a derivation for **every** `n : Nat`, not a finite approximation. The right iteration
rule uses a finite list of contexts, including the empty list. Multiplexing on the
left also permits `n = 0`.

Important naming distinction: the Lean helper `foc` denotes a canonical marking
obtained by scanning the antecedent. The dissertation's current notation `foc`
denotes the *initial* marking; this corresponds to **Lean `root`**, not Lean `foc`.
Their equivalence is proved by `root_iff_foc`.

The negative-formula replacement and continuation arguments correspond to
`replace_negative`, `replacement_admissible`, and `focused_continuation`.
The written proof and the Lean proof are not a line-by-line translation.
Checking Lean verifies the encoded statement relative to the encoded definitions;
comparison of these definitions with the mathematical calculus remains a human
review task.

## Reproduce the checks

Install [elan](https://lean-lang.org/install/manual/), then open a terminal in this
repository's root directory and run:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
```

`lean-toolchain` pins **Lean 4.19.0**. The first command compiles the whole proof.
The second checks the universally quantified theorem specification and requires
these exact axiom dependency lists:

```text
'Focusing.focusing_complete' depends on axioms: [propext, Quot.sound]
'Focusing.focusing' depends on axioms: [propext, Quot.sound]
```

These are standard Lean axioms (propositional extensionality and quotient
soundness). The audit fails if the output changes, including if `sorryAx` or a
user-added axiom appears. An empty successful audit output is normal:
`#guard_msgs` consumes the expected messages. Both commands must exit successfully.
The GitHub Actions workflow runs the same build and audit without a build cache.
Its actual result is visible under the repository's **Actions** tab.

To reproduce a cited release, first check out that release's exact commit, then run
these commands. No `lake update` or Mathlib cache download is needed.

## Authorship and provenance

Mathematical result and project maintainer: **Tikhon Pshenitsyn**.
The Lean formalization and accompanying documentation were prepared with
substantial assistance from OpenAI ChatGPT. This disclosure describes the creation
process; mathematical validity is assessed through the specification, definitions,
and reproducible Lean checks, rather than generated explanations alone.

## Citation and releases

This package is intended as version **1.0.0**. It does not yet contain an archive
DOI. After publishing and archiving a verified release in Zenodo, cite the DOI of
that **specific version**, and record its Git commit in the release description.
Add the DOI and repository URL to `CITATION.cff` when known. Do not invent a DOI.
Later corrections should be released as new versions rather than replacing the
archived version cited by the dissertation.

## License

MIT; see `LICENSE`.
