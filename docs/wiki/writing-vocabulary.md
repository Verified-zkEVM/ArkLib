# Writing Vocabulary

Use this page with the [writing standard](writing.md). STE's general dictionary remains the
reference for general words, meanings, and grammatical roles. This page adds subject-field terms
and advice for ArkLib prose. It is not a replacement for the dictionary or a list of every permitted
English word.

## How to add a term

1. Find the concept in Mathlib, Lean documentation, or its mathematical source.
2. Prefer the established term over a local synonym.
3. Record the intended meaning and grammatical role when the word can cause ambiguity.
4. Use a qualifier when two technical meanings occur in the same passage.
5. Add a missing term or meaning when the contribution first needs it.

A noun and a verb need separate technical uses, even when they have the same spelling. Listing
"query" as a noun does not approve every verb use of that word. A category example is not a reason
to reject another established term from that field.

## Terms and context

These distinctions help a reader identify the intended concept. They do not prohibit the ordinary
meaning of a word in a different context:

| Term | Technical use | Clarify when necessary |
|---|---|---|
| admission | A `sorry` or `admit` on which a declaration depends | Distinguish an admitted result from a proved result. |
| bound | A numerical or order constraint, as a noun | As a technical verb, state which quantity it bounds. |
| check | A test or condition, as a noun | As a software verb, it means to evaluate a specified condition or test. |
| code | An error-correcting code in coding theory | Use "source code" or "implementation" when both meanings occur. |
| complete, completeness | The completeness property of a proof system | Ordinary uses such as "complete the template" remain permitted. Name the property in security text. |
| error | A discrepancy, failure, or mathematical error quantity | Write "soundness error", "build error", or "error in the argument" when the context is ambiguous. |
| field | An algebraic field or a member of a structure | Write "structure field" when the distinction matters. |
| instance | A typeclass instance or a mathematical problem instance | Qualify the problem or typeclass when both occur. |
| module | A Lean module or an algebraic module | Write "Lean module" or "module over `R`" when the distinction matters. |
| proof | A mathematical proof, Lean proof, or proof-system object | Name the kind of proof before comparing different kinds. Do not call an arbitrary protocol object a string. |
| sound, soundness | A specified soundness property in security text | Name the property and its assumptions. Ordinary prose can use "correct" for an argument. |
| statement | A theorem's proposition or a protocol's public input | Use "theorem statement" or "protocol statement" when both meanings occur. |
| valid | Satisfaction of a specified predicate or well-formedness condition | Define or name the predicate. Do not replace "valid transcript" with "accepted transcript" unless they mean the same thing. |
| verify | A protocol verifier's action or a formal-verification operation | Use "check" for routine repository tests. Identify the relevant verification predicate or result. |

## Technical nouns

These examples identify relevant subject fields. Preserve established terms and their spellings.
Introduce a longer or unfamiliar term before using an abbreviation:

| Field | Examples |
|---|---|
| Algebra | field, ring, module, polynomial, multilinear extension, tensor product, coefficient, degree |
| Coding theory | code, codeword, Reed–Solomon code, generator matrix, relative distance, decoding radius, folding |
| Proximity | proximity gap, correlated agreement, mutual correlated agreement, Johnson bound |
| Probability | distribution, probability, event, random variable, sample, union bound |
| Protocols | prover, verifier, oracle, query, transcript, relation, statement, witness, reduction, extractor |
| Security | soundness, knowledge soundness, round-by-round soundness, completeness, soundness error, zero knowledge |
| Commitments | commitment scheme, commitment, opening, binding |
| Lean | declaration, theorem, lemma, hypothesis, docstring, namespace, typeclass, tactic, elaboration, axiom |
| Repository tools | branch, commit, pull request, build, linter, axiom baseline, validation, CI |

## Technical verbs

Use these verbs for the stated subject-field actions. Keep a verb's meaning consistent within a
passage. Explain the operation or name the relevant declaration when its meaning is not clear:

| Field | Examples of actions |
|---|---|
| Mathematics | prove a claim, define an object, assume a hypothesis, bound a quantity, evaluate a polynomial, interpolate values |
| Coding theory | encode a message, decode a word, fold a codeword, sample a challenge |
| Protocols | commit to data, query an oracle, accept an input, extract a witness, simulate a transcript, compose reductions |
| Lean | instantiate a variable, specialize a theorem, unfold a definition, rewrite an expression, elaborate a term, compile a module |
| Repository tools | build a target, run a linter, validate a change, rebase a branch, merge a PR, stage a file, review a contribution |

## Words to avoid

This table gives prompts for an editing pass over ordinary prose. They do not define STE word approval. Use a
replacement only when it preserves the meaning and grammatical role. Rewrite the sentence when a
direct replacement does not work:

| Avoid | Use |
|---|---|
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that, or name the condition and the action |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some", if the quantity is not specified |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t.", "wlog" | compare, explicit pairings, with respect to, without loss of generality |
| "respectively" | explicit pairings when the reference would otherwise be unclear |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial" | the measurement or the reason |
| "clearly", "obviously", "trivially", "basically" | the reason, or delete the word |
| "it is worth noting that", "it is important to" | delete the phrase when it adds no information |
| "now", "no longer", "previously", "formerly", "currently", "new" | in library reference text, the fact about the present state (rule C3) |

"The following are equivalent" is a permitted mathematical introduction. Words such as "simply"
and "essentially" can occur in technical terms, including "simply connected" and "essentially
surjective". Review their meaning rather than deleting them as isolated words.
