(ns cogito.core
  "
Cogito
======

*Cogito* is a Clojure implementation of **System-Z+**, a probabilistic reasoner described in [*\"Qualitative probabilities for default reasoning, belief revision, and causal modeling\"*](ftp://ftp.cs.ucla.edu/pub/stat_ser/R161-L.pdf) by Moises Goldszmidt and Judea Pearl.

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

Functions
=========
"
  (:require [clojure.contrib.combinatorics :as comb]))

(defn antecedent
  "Returns the antecedent of the given rule."
  ([rule] (first rule)))

(defn consequent
  "Returns the consequent of the given rule."
  ([rule] (second rule)))

(defn bool?
  "Determines if the logical variable is associated with a boolean value, where logical variables are represented by Clojure keywords, e.g. :x, :y."
  ([x]
     (= (type x) java.lang.Boolean)))

(defn negated?
  "Determines if the variable has been negated.

**Examples**

    (negated? :x) ;=> false
    (negated? [:not :x]) ;=> true
"
  ([x]
     (and (vector? x) (= (first x) :not))))

(defn state
  "Returns the state of the logical variable in the model, where a model consists of a map of logical variables and their associated truth values.

**Examples**

    (state {:a true, :b false} :a) ;=> true
    (state {:a true, :b false} [:not b]) ;=> true
"
  ([model x]
     (if (negated? x)
       (not (model (second x)))
       (model x))))

(defn get-var
  "Returns the logical variable's name.

**Examples**

    (get-var :x) ;=> :x
    (get-var [:not :x]) ;=> :x
"
  ([x]
     (if (negated? x) (second x) x)))

(defmulti assoc-state
    "Associates a truth-value(s) with a logical variable, or a pair of truth-values with a rule in the given model.

**Examples**

    (assoc-state {} :a true) ;=> {:a true}
    (assoc-state {} [:not :b] true) ;=> {:b false}

    (assoc-state {} [:a :b] [true false]) ;=> {:a true, :b false}
"
  (fn [model term p]
    (coll? p)))

(defmethod assoc-state false
  ([model term p]
     (assoc model (get-var term)
	    (if (negated? term) (not p) p))))


(defmethod assoc-state true
  ([model rule [x y]]
     (-> {}
	 (assoc-state (antecedent rule) x)
	 (assoc-state (consequent rule) y))))

(defn update-bindings
  "
Updates model with new bindings based on the given rule. One or more bindings in the model will have a value of :inconsistent, if the new rule is inconsistent with the current model.

New values are only added to the model if the antecedent, 'a',  is already bound to true, then the value of 'b' is set to true if isn't bound yet, set to :inconsistent if it is already bound to false, otherwise it is left as is.

"
  ([model [a b :as rule]]
     (if (true? (state model a))
       (cond
	(false? (state model b)) (assoc model (get-var b) :inconsistent)
	(nil? (state model b)) (assoc-state model b true)
	:else model)
       model)))

(defn append-rule
  "
Returns the model created by adding rule to rule-set. A logical variable in the model will have a truth-value of :inconsistent if the new rule is not tolerated in the rule-set.

This method:

1. Sets the logical variables associated with the  antecedent and consequent of the rule to true in the model.
2. Walks through the rest of rules in a non-deterministic order and applying update-bindings to the model for each.
   * For each rule whose antecedent is already true in the model, its consequent is also set to true if it is currently nil, :inconsistent if its set to false, otherwise it's not changed.
   * Rules that could not be applied because their antecedents were false in the model are placed back at the end of the list of rules, possibly to be applied again once other bindings are in place.
   * Rules that don't change the state of the model because their antecendents and consequents were already true are not applied again.
   * When the model is updated after a new rule is applied all unapplied rules are attempted again.
"
  ([rule-set rule]
     (append-rule rule-set rule (assoc-state {} rule [true true])))
  ([rule-set rule model]
     (let [[a b] rule]
       (loop [m model
	      rules rule-set
	      unapplied-rules []]
	 (if (seq rules)
	   (let [r (first rules)
		 new-m (if (= rule r) m (update-bindings m r))]
	     (cond
	      (not= new-m m) 
  	        (recur new-m (concat unapplied-rules (rest rules)) [])
	      (true? (state new-m (antecedent r))) 
	        (recur new-m (rest rules) unapplied-rules)
	      :else
	        (recur new-m (rest rules) (conj unapplied-rules r))))
	   m)))))

(defn tolerate?
  "Determines if a rule is tolerated by an existing rule-set, an optional model can be provided as well"
  ([rule-set rule]
     (not ((set (vals (append-rule rule-set rule))) :inconsistent)))
  ([rule-set rule model]
     (not ((set (vals (append-rule rule-set rule model))) :inconsistent))))

(defn partition-by-consistency
  "
Partitions a set of rules into a set of groups orderd from general to specific, where the rules in each group are tolerated by all the rules in its group as well as all later groups.

If the rule-set cannot be partitioned such, then it is inconsistent and nil will be returned.

Each group forms a sub-theory, where earlier groups are more general and later groups are more specific.

**Notes**

See *Figure 2 Procedure for testing consistency* in Goldszmidt and Pearl.
"
  ([rule-set]
     (let [f (fn [rule-set] (set (filter #(tolerate? rule-set %) rule-set)))]
       (loop [parts [] rules rule-set]
	 (if (seq rules)
	   (let [new-part (f rules)]
	     (if (seq new-part)
	       (recur (conj parts new-part)
		      (apply clojure.set/difference rule-set new-part parts))
	       nil))
	   parts)))))

(defn extract-vars
  "Extracts logical variable names from a rule set."
  ([rule-set]
     (set (mapcat (fn [r] (map get-var r)) rule-set))))

(defn generate-all-models
  "Generates all models possible for a given rule-set, even inconsistent models."
  ([rule-set]
     (let [vars (extract-vars rule-set)
	   truth-vals (comb/selections [true false] (count vars))]
       (map #(zipmap vars %) truth-vals))))

(defn entails?
  "Determines if a set of truth-conditions are entailed by a given model."
  ([model truth-condition]
     (= truth-condition (select-keys model (keys truth-condition)))))

(defn filter-models
  "Filters a set of models so that only those consistent with the given truth-condition are returned."
  ([models truth-condition]
     (filter #(= truth-condition (select-keys % (keys truth-condition))) models)))

(defn z-plus-order
  "
****
Z+-order algorithm
===================

1. Partition rules into ordered groups, where the rules in each successive group do not conflict with the rules in later groups.
2. Assign Z(r) scores to each rule in the first group equal to their individual delta values.
3. For each rule in the next group, find all the models where its antecedent is true and that are not in conflict with any other rule in the group.
  * From these models select models that conflict with any of rules in the first group and calculate their Z(r) score.
  * Choose the score from the model with the maximum value and add 1 to the value, and do the same for each other model.
  * Now choose the score from the model with the minimum score and add the delta value associated with the rule to determine the rule's Z(r) score.
4. Take the rule with the lowest Z(r) score and add it to the first group.
5. Repeat the procedure for each rule in the current group, and then move to the next group.

****
**Example**

    (def rules #{[:b :f]
 	         [:p :b]
	         [:p [:not :f]]
	         [:b :w]
	         [:f :a]})

    (def parts (partition-by-consistency rules))

    ;;=> [#{[:b :f] [:b :w] [:f :a]} #{[:p :b] [:p [:not :f]]}]

    (def z-ordered-rules (z-plus-order (first parts)
                                       (second parts)))

    ;;=> {[:p :b] ([:b :f]), [:p [:not :f]] ([:b :f])}

"
  ([rz-plus _Delta-star]
     (let [_Omega-r (apply merge
			   (map (fn [r]
				  {r (filter (fn [model]
					       (tolerate? _Delta-star r model))
					     (filter-models (generate-all-models _Delta-star)
							     (assoc-state {} r [true true])))})
				_Delta-star))]
       (apply merge
	      (map (fn [[r-star omega-r]]
		     {r-star (mapcat (fn [model]
				       (reduce (fn [out rz-rule]
						 (if (entails? model (assoc-state {} rz-rule [true false]))
						   (conj out rz-rule)
						   out))
					       [] rz-plus))
				     omega-r)})
		   _Omega-r)))))


