Cogito
======

*Cogito* is a Clojure implementation of **System-Z+**, a probabilistic reasoner described in [*"Qualitative probabilities for default reasoning, belief revision, and causal modeling"*](ftp://ftp.cs.ucla.edu/pub/stat_ser/R161-L.pdf) by Moises Goldszmidt and Judea Pearl.

Documentation
=============

[Marginalia](https://github.com/fogus/marginalia)-generated documentation is available at <http://liebke.github.com/cogito>.


Overview
========

The basic idea is that you create a rule map, where keys are pairs of antecedents and consequents, each associated with an integer value, delta, that determines the strength of the connection between the pair

    {[:b :f] 1
     [:p :b] 1
     [:p [:not :f]] 1
     [:b :w] 1
     [:f :a] 1}

The system then automatically scores and orders the rules from most general (i.e. not inconsistent with any other rules) to most specific (i.e. inconsistent with one or more earlier rules). More specific rules will have higher scores than more general rules, where the score represents the surprise associated with a violation of the rule.

Below is an example of partitioning the above rules based on a consistency test (figure 2 Goldszmidt and Pearl). The rules in the first group are tolerated by all the rules in the rule set, whereas the rules in the second group are not tolerated by those in the first group.

    [#{[:b :f] [:b :w] [:f :a]}
     #{[:p :b] [:p [:not :f]]}]

Once partitioned scores are assigned to each rule. First the scores of the rules in the first group are set equal to the delta values associated with each of the rules. Next each rule in later groups are evaluated to determine which rules they violate in the first group. The z-plus-order function returns map showing which rules are violated.

    {[:p :b] ([:b :f]),
     [:p [:not :f]] ([:b :f])}

In the above case, both rules in the second group only violate one rule in the first group, [:b :f], which states that birds fly. The scores for these two rules will then be set equal to their respective delta values plus the score for the [:b :f] rule plus one, meaning violating more specific (i.e. later) rules will be associated with more surprise than violating more general ones.

The difference between the delta value and the score associated with each rule is that delta only represents the strength between the given antecedent and consequent, whereas the score takes all the other rules into consideration.

Queries are made by submitting competing hypotheses, the one that is the least surprising (i.e. has the lowest score associated with it) is selected.

****
**Example**

The following example takes the above rules-map, compiles it, and runs several queries (each compare two competing hypotheses), which returns a map that associates a \"surprise\" score with each hypothesis, the lowest score wins.

A hypothesis is a model (map of truth values) formed from a logical statement. For instance, a statement

    penguins ^ birds -> fly

can be read as \"penguin birds can fly\" and can be represented in a truth-value map as:

    {:p true, :b true, :f true}

The following rules,

* birds fly
* penguins are birds
* penguins cannot fly
* birds have wings
* flying implies airborn

can be translated to the following rules-map.

    (def rules-map {[:b :f] 1
                    [:p :b] 1
                    [:p [:not :f]] 1
                    [:b :w] 1
                    [:f :a] 1})

All of the rules have a delta-value of one, these values can be adjusted if not all the rules have the same \"strength\".

Next compile the rules-map,

    (def compiled-rules (compile-rules rules-map))

and then run the following queries against it.

**Do penguin birds fly?**

This query is submitted by creating two hypotheses, one where penguin birds fly and one where they don't.

    (query compiled-rules
           {:p true, :b true, :f true}
           {:p true, :b true, :f false})

The results are that flying penguins that more surprising than non-flying ones.

    penguins ^ birds -> fly    (score)
    ----------------------------------
    true       true     true   (3)
    true       true     false  (1)


**Are all birds penguins?**

    (query compiled-rules
           {:b true, :p true}
           {:b true, :p false})

The results are that not all birds are penguins.

    birds -> not penguins    (score)
    --------------------------------
    true     not true        (0)
    true     not false       (1)


**Do red birds fly?**

    (query compiled-rules
           {:r true, :b true, :f true}
           {:r true, :b true, :f false})


The results are that red birds do fly.

    red ^ birds -> fly    (score)
    -----------------------------
    true  true     true   (0)
    true  true     false  (1)


**Are birds airborn?**

    (query compiled-rules
           {:b true, :a true}
           {:b true, :a false})

The results are that birds are airborn.

    birds -> airborn    (score)
    --------------------------
    true     true       (0)
    true     false      (1)


**Do penguins have wings?**

    (query compiled-rules
           {:p true, :w true}
           {:p true, :w false})


This is a known area of weakness for System-Z+, it cannot decide whether penguins have wings.

    penguins -> wings    (score)
    ----------------------------
    true        true     (1)
    true        false    (1)



Build It
========

Either:

    script/build.sh
    script/build-docs.sh

Or:

    lein deps
    lein test
    lein marg
