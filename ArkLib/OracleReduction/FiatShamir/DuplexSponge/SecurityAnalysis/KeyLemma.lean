import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Basic

/-!
# Lemma 5.1 of the Chiesa-Orrù paper

We give the statement (and eventually, proof) of this key lemma, which states that two games
(duplex-sponge vs. basic Fiat-Shamir) have the same distribution, up to two auxiliary procedures
that transform the prover and the query-answer traces, respectively.

Using this key lemma, we can easily conclude preservation of (knowledge) soundness.
-/
