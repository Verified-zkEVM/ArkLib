# Writing Vocabulary

This page lists the vocabulary for ArkLib prose. It supports rules W1 to W3 of the
[writing standard](writing.md). The STE dictionary does not cover mathematics. Thus ArkLib uses the
STE method for a subject field: a list of technical nouns and technical verbs. The page also lists
the terms that have one fixed meaning, and the words to avoid.

The lists are a starting set. Add a term in the pull request that first needs it.

## How to add a term

1. Make sure that no listed term already names the concept.
2. Select the term that Mathlib or the literature uses.
3. Give the term one meaning in ArkLib prose.
4. If the field gives the word other meanings, write the term for each other meaning.
5. Add the term to the applicable table on this page.

## Terms with one fixed meaning

Some words have two meanings in ArkLib. Use each word below only with the meaning in the second
column. For the other meaning, use the term in the third column.

| Term | Meaning in ArkLib prose | For the other meaning, write |
|---|---|---|
| admission | A `sorry` or `admit` that a declaration depends on | Not applicable |
| bound | An upper or lower bound (noun), or to give one (verb) | Not applicable |
| check | A test that a person or a tool runs | "verify" only for a verifier in a protocol |
| code | An error-correcting code, in coding-theory text | "source" or "implementation" for a program |
| complete, completeness | The completeness property of a proof system | "finished" or "done" |
| error | The soundness error or the knowledge error, with that qualifier | "build error" or "elaboration error" |
| field | An algebraic field | "structure field" for a field of a Lean structure |
| instance | A typeclass instance | "statement" for the input of a relation |
| module | A Lean module (one source file) | "`R`-module" or "module over `R`" for the algebraic object |
| proof | A Lean proof or a paper proof | "proof string" or the message type for the output of a proof system |
| sound, soundness | The soundness property of a proof system | "correct" for a correct argument |
| statement | The public input of a relation | "theorem statement" for the type of a theorem |
| verify | The action of a verifier in a protocol | "check" for a person or a tool |

## Technical nouns

The nouns below are examples for each category. A noun that fits a category is permitted, also
when this list does not include it.

| Category | Examples |
|---|---|
| Algebra | field, ring, module, polynomial, multilinear extension, tensor product, evaluation, coefficient, degree, root |
| Coding theory | code, codeword, Reed–Solomon code, generator matrix, distance, relative distance, rate, list size, decoding radius, interleaving, folding |
| Proximity | proximity gap, correlated agreement, mutual correlated agreement (MCA), Johnson bound, agreement set |
| Probability | distribution, probability, event, union bound, random variable, sample |
| Protocols | prover, verifier, oracle, query, round, challenge, transcript, relation, statement, witness, reduction, oracle reduction, extractor, simulator, adversary |
| Security | soundness, knowledge soundness, round-by-round soundness, completeness, soundness error, zero knowledge |
| Commitments | commitment scheme, commitment, opening, binding |
| Lean and Mathlib | declaration, definition, theorem, lemma, hypothesis, docstring, namespace, typeclass, instance, tactic, elaboration, axiom, admission |
| Repository and tools | branch, commit, pull request, base, build, warning, warning budget, linter, axiom baseline, validation, CI |

## Technical verbs

These verbs are permitted with the meaning that the field gives them.

| Category | Verbs |
|---|---|
| Mathematics | prove, define, assume, hold, imply, bound, satisfy, evaluate, interpolate, encode, decode, fold, batch, sample |
| Protocols | commit, open, query, accept, reject, extract, simulate, compose, lift |
| Lean | instantiate, specialize, generalize, unfold, rewrite, simplify, elaborate, compile, admit |
| Repository and tools | build, lint, validate, rebase, merge, push, stage, review |

## Words to avoid

The words in the first column make text longer, less exact, or less literal. Use the word in the
second column.

| Avoid | Use |
|---|---|
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some" |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t.", "wlog" | compare, two separate clauses, with respect to, without loss of generality |
| "respectively" | two separate clauses |
| "the following" | these, or "that follow" |
| "valid" | the exact predicate, for example "accepted" or "in the code" |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial" | the measurement or the reason |
| "clearly", "obviously", "trivially", "simply", "basically", "essentially" | the reason, or delete the word |
| "note that", "it is worth noting that", "it is important to" | delete the phrase |
| "now", "no longer", "previously", "formerly", "currently", "new" | in Lean files and in the wiki, the fact about the present state (rule C3) |
