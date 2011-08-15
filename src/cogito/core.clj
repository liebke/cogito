(ns cogito.core
  "
Cogito
======

*Cogito* is a Clojure implementation of **System-Z+**, a qualitative-probabilistic reasoner described in [*\"Qualitative probabilities for default reasoning, belief revision, and causal modeling\"*](ftp://ftp.cs.ucla.edu/pub/stat_ser/R161-L.pdf) by Moises Goldszmidt and Judea Pearl.

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


Example
=======

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


"
  (:require [clojure.contrib.combinatorics :as comb]))

(defn to-model
  "
****
"
  ([term] (if (keyword? term) #{{term true}} term))
  ([term value] (if (keyword? term) #{{term value}} term)))

(defn generate-all-models-for-vars
  "
****
Generates all models possible for a given set of logical variables, even inconsistent models."
  ([vars]
     (let [truth-vals (comb/selections [true false] (count vars))]
       (map #(zipmap vars %) truth-vals))))

(defn merge-truth-values
  "
****
"
  ([& models]
     (reduce #(merge-with (fn [val1 val2] (if (not= val1 val2) :inconsistent val1)) %1 %2)
	     {} models)))

;; Logical Operation Functions
;; ===========================

(defn $not
  "
****
**Examples**

    ($not :a)
    ;; => #{{:a false}}

    ($not [{:a true, :b true}])
    ;; => #{{:b false, :a false} {:b false, :a true} {:b true, :a false}}
"
  ([term]
     (if (keyword? term)
       (to-model term false)
       (seq (clojure.set/difference (set (generate-all-models-for-vars (keys (first term))))
				    (set term))))))

(defn $and
  "
****
**Examples**

    ($and ($not :a) ($not :b))
    ;; =>({:b false, :a false})

    ($and :a ($not [{:b false, :d true} {:b false, :d false}]))
    ;; => ({:b true, :d true, :a true} {:b true, :d false, :a true})

    ($and ($not [{:a true :c true} {:a true :c false}]) ($not [{:b false, :d true} {:b false, :d false}]))
    ;; => ({:b true, :d true, :a false, :c true} {:b true, :d false, :a false, :c true} {:b true, :d true, :a false, :c false} {:b true, :d false, :a false, :c false})

    ($and ($not [{:a true :c true} {:a true :c false}]) ($not [{:a false, :d true} {:a false, :d false}]))
    ;; => ({:d false, :a :inconsistent, :c true} {:d true, :a :inconsistent, :c true} {:d false, :a :inconsistent, :c false} {:d true, :a :inconsistent, :c false})

    ($and ($not [{:a true :c true} {:a true :c false}]) ($not [{:a true, :d true} {:a true, :d false}]))
    ;; => ({:d false, :a false, :c true} {:d true, :a false, :c true} {:d false, :a false, :c false} {:d true, :a false, :c false})


"
  ([term & terms]
     (reduce (fn [a b]
	       (filter #(-> % vals set :inconsistent not)
		      (map #(apply merge-truth-values %)
			   (comb/cartesian-product (to-model a) (to-model b)))))
	     term terms)))

(defn $or
  "
****
**Examples**

    ($or :a :b)
    ;; =>

    ($or ($not :a) ($not :b))
    ;; =>

    ($or :a ($not [{:b false, :d true} {:b false, :d false}]))
    ;; => 

    ($or ($not [{:a true :c true} {:a true :c false}]) ($not [{:b false, :d true} {:b false, :d false}]))
    ;; => 

    ($or ($not [{:a true :c true} {:a true :c false}]) ($not [{:a false, :d true} {:a false, :d false}]))
    ;; => 

    ($or ($not [{:a true :c true} {:a true :c false}]) ($not [{:a true, :d true} {:a true, :d false}]))
    ;; => 



"
  ([term & terms]
     (reduce (fn [a b] (concat ($and a b) ($and a ($not b)) ($and ($not a) b)))
	     term terms)))

(defn $=>
  "
****
"
  ([a b] ($or ($and a b) ($not a))))

(def logical-functions {:not $not, :and $and, :or $or, :=> $=>})

(defn find-all-models
  "
****

    (find-all-models [:not :a])
    (find-all-models [:and :a :b])
    (find-all-models [:or :a :b])
    (find-all-models [:=> :a :b])
    (find-all-models [:and [:not :a] :b])
    (find-all-models [:or [:not :a] :b])
    (find-all-models [:or [:and :a :b] [:and :c :d]])

"
  ([stmt]
     (if (keyword? stmt)
       (to-model stmt)
       (if-let [op (logical-functions (first stmt))]
	   (apply op (map #(find-all-models %) (rest stmt)))
	   stmt))))


;; Performance Notes
;; =================

;; Disjunction is much more expensive than conjunction, it's best to use alternative conjunction-based representations when possible.
;; Below is an example of equivalent statements, transformed by De Morgan's law, the conjunction-based version is nearly x600 faster.

;;    (time (count (find-all-models [:not [:or :a :b :c :d :e :f :g :h :i :j :k]])))
;;    => "Elapsed time: 574.026 msecs"
;;  
;;    (time (count (find-all-models [:and [:not :a] [:not :b] [:not :c] [:not :d] [:not :e] [:not :f] [:not :g] [:not :h] [:not :i] [:not :j] [:not :k]])))
;;    => "Elapsed time: 0.914 msecs"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn partition-rules
  "
****

    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (partition-rules rules-map)


    (partition-rules {[:=> :s [:not :w]] 1
                      [:=> :s :a] 1
                      [:=> :a :w] 1})

"
  ([rules-map]
     (let [rule-set (set (keys rules-map))
	   f (fn [rs]
	       (set (filter (fn [[_ a b :as rule]]
			      (-> [:and a b]
				  (concat (clojure.set/difference rs #{rule}))
				  find-all-models
				  seq))
			    rs)))]
       (loop [parts [] rules rule-set]
         (if (seq rules)
           (let [new-part (f rules)]
             (if (seq new-part)
               (recur (conj parts new-part)
                      (apply clojure.set/difference rule-set new-part parts))
               nil))
           parts)))))

(defn find-conflicting-rules
  ""
  ([rules-part1 rules-part2]
     (apply merge-with concat
	    (for [[_ e f :as ir] rules-part1
		  [_ a b :as cr] rules-part2]
	      (when (-> [:and a b e [:not f]]
			(concat rules-part2)
			find-all-models
			seq)
		{cr [ir]})))))

(defn update-rules-map
  "
Updates the score in the rules-map based on the z-plus-order algorithm.

**Examples**

    (def parts (partition-rules rules-map))
    (update-rules-map rules-map (first parts) (second parts))

"
  ([rules-map rules-part1 rules-part2]
     (let [conflicts (find-conflicting-rules rules-part1 rules-part2)]
       (apply merge rules-map
	      (map (fn [cr]
		     {cr (+ 1 (rules-map cr)
			    (apply max (map (fn [ir] (or (rules-map ir) 0))
					    (conflicts cr))))})
		   (keys conflicts))))))

(defn score-rules
  "
****
Given a map associating rules to delta-values, returns a new map containing two keys, :delta-values (which is associated with the original map) and :z+-scores (which is associated with a map containing a \"surprise\" score for each rule).

This compiled-rules map can be passed to the query function as an alternative to an uncompiled rules-map.

**Examples**

    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (def scored-rules (score-rules rules-map))

    (def scored-rules2 (score-rules {[:=> :s [:not :w]] 1
                                     [:=> :s :a] 1
                                     [:=> :a :w] 1}))

 "
  ([rules-map]
     (when-let [[part0 & parts] (map seq (partition-rules rules-map))]
       (:scores (reduce (fn [{:keys [scores updated-rules]} part]
			  {:scores (update-rules-map scores updated-rules part)
			   :updated-rules (concat updated-rules part)})
			{:scores rules-map, :updated-rules part0} parts)))))


(defn score-models-for-hypothesis
  "
****
For a given hypothesis, score each model that is consistent with it based on the score associated with each rule it violates.

**Examples**

    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (def scored-rules (score-rules rules-map))

    (score-models-for-hypothesis scored-rules [:and [:and :p :b] [:not :f]]) ;; => 1
    (score-models-for-hypothesis scored-rules [:and [:and :p :b] :f]) ;; => 3

    (score-models-for-hypothesis scored-rules [:and :b [:not :p]]) ;; => 0
    (score-models-for-hypothesis scored-rules [:and :b [:not [:not :p]]]) ;; => 1

    (score-models-for-hypothesis scored-rules [:and [:and :r :b] :f]) ;; => 0
    (score-models-for-hypothesis scored-rules [:and [:and :r :b] [:not :f]]) ;; => 1

    (score-models-for-hypothesis scored-rules [:and :b :a]) ;; => 0
    (score-models-for-hypothesis scored-rules [:and :b [:not :a]]) ;; => 1

    (score-models-for-hypothesis scored-rules [:and :p :a]) ;; => 1
    (score-models-for-hypothesis scored-rules [:and :p [:not :a]]) ;; => 1

    (score-models-for-hypothesis scored-rules [:and :p :w]) ;; => 1
    (score-models-for-hypothesis scored-rules [:and :p [:not :w]]) ;; => 3

    (def scored-rules2 (score-rules {[:=> :s [:not :w]] 1
                                     [:=> :s :a] 1
                                     [:=> :a :w] 1}))

    (score-models-for-hypothesis scored-rules2 [:and :a :s]) ;; => 1
    (score-models-for-hypothesis rules2 [:and :a [:not :s]]) ;; => 0

    (score-models-for-hypothesis rules2 [:and [:and :s :a] :w]) ;; => 3
    (score-models-for-hypothesis rules2 [:and [:and :s :a] [:not :w]]) ;; => 1

    (score-models-for-hypothesis rules2 [{:a true}])
    (score-models-for-hypothesis rules2 [:not :a]) 



"
  ([scored-rules hypothesis]
     (let [rules-set (set (keys scored-rules))
	   models (-> [:and hypothesis]
		      (concat rules-set)
		      find-all-models)
	   model-scores (zipmap models (repeat (count models) 0))
	   score-inconsistent-models (fn [[_ a b :as rule]]
				       (when-let [inconsistent-models (-> [:and hypothesis a [:not b]]
									  (concat (clojure.set/difference rules-set #{rule}))
									  find-all-models
									  seq)]
					 (zipmap inconsistent-models
						 (repeat (count inconsistent-models)
							 (scored-rules rule)))))]
       (->> (map #(score-inconsistent-models %) rules-set)
	    (apply merge-with max model-scores)))))

 (defn score-hypothesis
   "
    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (def scored-rules (score-rules rules-map))

    (score-hypothesis scored-rules [:and [:and :p :b] [:not :f]]) ;; => 1
    (score-hypothesis scored-rules [:and [:and :p :b] :f]) ;; => 3

    (score-hypothesis scored-rules [:and :b [:not :p]]) ;; => 0
    (score-hypothesis scored-rules [:and :b [:not [:not :p]]]) ;; => 1

    (score-hypothesis scored-rules [:and [:and :r :b] :f]) ;; => 0
    (score-hypothesis scored-rules [:and [:and :r :b] [:not :f]]) ;; => 1

    (score-hypothesis scored-rules [:and :b :a]) ;; => 0
    (score-hypothesis scored-rules [:and :b [:not :a]]) ;; => 1

    (score-hypothesis scored-rules [:and :p :a]) ;; => 1
    (score-hypothesis scored-rules [:and :p [:not :a]]) ;; => 1

    (score-hypothesis scored-rules [:and :p :w]) ;; => 1
    (score-hypothesis scored-rules [:and :p [:not :w]]) ;; => 3


    (def scored-rules2 (score-rules {[:=> :s [:not :w]] 1
                                     [:=> :s :a] 1
                                     [:=> :a :w] 1}))

    (score-hypothesis scored-rules2 [:and :a :s]) ;; => 1
    (score-hypothesis scored-rules2 [:and :a [:not :s]]) ;; => 0

    (score-hypothesis scored-rules2 [:and [:and :s :a] :w]) ;; => 3
    (score-hypothesis scored-rules2 [:and [:and :s :a] [:not :w]]) ;; => 1


 "
   ([scored-rules hypothesis]
     (->> (score-models-for-hypothesis scored-rules hypothesis)
	  vals
	  (apply min))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Query Functions
;; ===============

(defn compile-rules
  "
****
Given a map associating rules to delta-values, returns a new map containing two keys, :delta-values (which is associated with the original map) and :z+-scores (which is associated with a map containing a \"surprise\" score for each rule).

This compiled-rules map can be passed to the query function as an alternative to an uncompiled rules-map.

**Examples**

    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (compile-rules rules-map)

"
  ([rules-map]))

(defn query 
  "
****
Given either an uncompiled or compiled rules map and a series of hypothetical models, returns a map associating each hypothesis with a \"surprise\" score (i.e. the lowest score is the most likely).

**Examples**

    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (def scored-rules (score-rules rules-map))

    ;; penguins ^ birds -> fly
    (query scored-rules
           [:and :p :b :f]
           [:and :p :b [:not :f]])

    ;; birds -> not penguins
    (query scored-rules
           [:and :b :p]
           [:and :b [:not :p]])

    ;; red ^ birds -> fly
    (query scored-rules
           [:and :r :b :f]
           [:and :r :b [:not :f]])

    ;; birds -> airborn
    (query scored-rules
           [:and :b :a]
           [:and :b [:not :a]])

    ;; undecided
    (query scored-rules
           [:and :p :w]
           [:and :p [:not :w]])

"
  ([scored-rules-map & hypotheses]
     (reduce #(assoc %1 %2 (score-hypothesis scored-rules-map %2)) {} hypotheses)))

(defn entailed
  "
****
Returns a map of scores for the valid hypotheses associated with the given antecedent and consequent.

    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (def scored-rules (score-rules rules-map))

    (entailed scored-rules [:and :p :b] :f)
    ;;=> {{:b true, :p true, :f true} 3, {:f false, :p true, :b true} 1}

    (entailed scored-rules :b [:not :p])
    ;;=> {{:p true, :b true} 1, {:b true, :p false} 0}

    (entailed scored-rules [:and :r :b] :f)
    ;;=> {{:b true, :r true, :f true} 0, {:f false, :r true, :b true} 1}

    (entailed scored-rules :b :a)
    ;;=> {{:a false, :b true} 1, {:b true, :a true} 0}

    (entailed scored-rules :p :w)
    ;;=> {{:w false, :p true} 1, {:p true, :w true} 1}

    (entailed rules [:or :b :p] :f)
    ;;=> {{:p true, :b true, :f true} 3,
          {:p false, :b true, :f true} 0,
          {:f false, :b true, :p true} 1,
          {:p true, :b false, :f true} 3,
          {:f false, :b true, :p false} 1,
          {:f false, :b false, :p true}} 3

"
  ([rules antecedent consequent]
     (query scored-rules [:and antecedent consequent] [:and antecedent [:not consequent]])))

(defn entailed?
  "
****
Returns a boolean indicating whether the given consequent is entailed from the antecendent and rules.

    (def rules-map {[:=> :b :f] 1
                    [:=> :p :b] 1
                    [:=> :p [:not :f]] 1
                    [:=> :b :w] 1
                    [:=> :f :a] 1})

    (def scored-rules (score-rules rules-map))

    (entailed? scored-rules [:and :p :b] :f) ;;=> false

    (entailed? scored-rules :b [:not :p]) ;;=> true

    (entailed? scored-rules [:and :r :b] :f) ;;=> true

    (entailed? scored-rules :b :a) ;;=> true

    (entailed? scored-rules :p :w) ;;=> nil

    (entailed? scored-rules [:or :b :p] :f) ;;=> true

"
  ([scored-rules antecedent consequent]
     (let [h0 (score-hypothesis scored-rules [:and antecedent [:not consequent]])
	   h1 (score-hypothesis scored-rules [:and antecedent consequent])]
      (cond
       (= h0 h1)
         nil
       (> h0 h1)
         true
       :else
         false))))

