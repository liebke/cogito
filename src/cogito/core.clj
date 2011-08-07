(ns cogito.core
  (:require [clojure.contrib.combinatorics :as comb]))

(defn bool? [x] (= (type x) java.lang.Boolean))

(defn negated?? [x]
  (and (vector? x) (= (first x) :not)))

(defn state [table x]
  (if (negated?? x)
    (not (table (second x)))
    (table x)))

(defn assoc-state [table x p]
  (if (negated?? x)
    (assoc table (second x) (not p))
    (assoc table x p)))

(defn get-var [x]
  (if (negated?? x)
    (second x)
    x))

(defn assoc-if-tolerates
  "Updates model to include new rule. One or more truth-values in the model will have a value of :inconsistent, if the new rule is inconsistent  with the current model."
  ([model [ai bi :as rule]]
     (if (true? (state model ai))
       (cond
	(true? (state model bi)) model
	(false? (state model bi))
          (assoc model (get-var bi) :inconsistent)
	(= (state model bi) :inconsistent) model  
	:else (assoc-state model bi true))
       model)))

(defn append-rule
  "Returns the model created by adding rule to rule-set. A logical variable in the model will have a truth-value of :inconsistent if the new rule is not tolerated in the rule-set."
  ([rule rule-set]
     (append-rule rule rule-set (reduce #(assoc-state %1 %2 true) {} rule)))
  ([rule rule-set model]
     (let [[a b] rule]
       (loop [t model
	      rules rule-set
	      unapplied-rules []]
	 (if (seq rules)
	   (let [r (first rules)
		 new-t (if (= rule r) t (assoc-if-tolerates t r))]
	     (if (> (count new-t) (count t))
	       (recur new-t (concat unapplied-rules (rest rules)) unapplied-rules)
	       (recur new-t (rest rules) (conj unapplied-rules r))))
	   t)))))

(defn tolerate?
  "Determines if a rule is tolerated by an existing rule-set, an optional model can be provided as well"
  ([rule rule-set]
     (not ((set (vals (append-rule rule rule-set))) :inconsistent)))
  ([rule rule-set model]
     (not ((set (vals (append-rule rule rule-set model))) :inconsistent))))

(defn partition-consistent
  "Partitions a set of rules into an orderd set of groups, where the rules in each group are tolerated by all the rules in its group as well as all later groups. If no rule is consistent with all other rules, then the rule-set is inconsistent. Each group forms a sub-theory, where earlier groups are more general and later groups are more specific."
  ([rule-set]
     (let [f (fn [rule-set] (set (filter #(tolerate? % rule-set) rule-set)))]
       (loop [parts [] rules rule-set]
	 (if (seq rules)
	   (let [new-part (f rules)]
	     (recur (conj parts new-part)
		    (apply clojure.set/difference rule-set new-part parts)))
	   parts)))))

(defn apply-priorities [partitions]
  (apply merge (for [i (range (count partitions))]
		 (zipmap (get partitions i) (repeat (count (get partitions i)) i)))))

(defn extract-vars [rule-set]
  (set (mapcat (fn [r] (map get-var r)) rule-set)))

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
# Z^+-order algorithm:
1. Partition rules into ordered groups, where the rules in each successive group do not conflict with the rules in later groups.
2. Assign Z(r) scores to each rule in the first group equal to their individual delta values.
3. For each rule in the next group, find all the models where its antecedent is true and that are not in conflict with any other rule in the group.
  * From these models select models that conflict with any of rules in the first group and calculate their Z(r) score.
  * Choose the score from the model with the maximum value and add 1 to the value, and do the same for each other model.
  * Now choose the score from the model with the minimum score and add the delta value associated with the rule to determine the rule's Z(r) score.
4. Take the rule with the lowest Z(r) score and add it to the first group.
5. Repeat the procedure for each rule in the current group, and then move to the next group.

# Example

 (def rules #{[:b :f]
 	      [:p :b]
	      [:p [:not :f]]
	      [:b :w]
	      [:f :a]})

 (def parts (partition-consistent rules))

 (def z-ordered-rules (z-plus-order (first parts) (second parts)))

"
  ([rz-plus _Delta-star]
     (let [_Omega-r (apply merge
			   (map (fn [r]
				  {r (filter (fn [model]
					       (tolerate? r _Delta-star model))
					     (filter-models (generate-all-models _Delta-star)
							     (reduce #(assoc-state %1 %2 true)
								     {} r)))})
				_Delta-star))]
       (apply merge
	      (map (fn [[r-star omega-r]]
		     {r-star (mapcat (fn [model]
				       (reduce (fn [out rz-rule]
						 (if (entails? model (zipmap rz-rule [true false]))
						   (conj out rz-rule)
						   out))
					       [] rz-plus))
				     omega-r)})
		   _Omega-r)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples

(def rules #{[:b :f]
	     [:p :b]
	     [:p [:not :f]]
	     [:b :w]
	     [:f :a]})

(def deltas (zipmap rules [1 1 1 1 1]))

(def parts (partition-consistent rules))

(def z-ordered-rules (z-plus-order (first parts) (second parts)))


;; examples
(append-rule [:b :f] rules)
(tolerate? [:b :f] rules)


(append-rule [:p :b] rules)
(tolerate? [:p :b] rules)


(append-rule [:p [:not :f]] rules)
(tolerate? [:p [:not :f]] rules)


(partition-consistent rules)

(apply-priorities (partition-consistent rules))





