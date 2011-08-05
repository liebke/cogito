(ns cogito.core
  (:require [clojure.contrib.combinatorics :as comb]))

(defn bool? [x] (= (type x) java.lang.Boolean))

(defn negated? [x]
  (and (vector? x) (= (first x) :not)))

(defn state [table x]
  (if (negated? x)
    (when  (bool? (table (second x)))
      (not (table (second x))))
    (table x)))

(defn get-var [x]
  (if (negated? x)
    (second x)
    x))

(defn assoc-truth-value [table x p]
  (let [truth-value (if (negated? x) (not p) p)]
    (assoc table (get-var x) truth-value)))

(defn assoc-state [table [a b :as rule]]
  (cond
   (true? (state table a))
     (cond
      (true? (state table b)) table
      (false? (state table b))
        (assoc table (get-var b) :inconsistent)
      (= (state table b) :inconsistent) table  
      :else (assoc-truth-value table b true))
   (nil? (state table a))
     (let [t (assoc-truth-value table a true)]
       (cond
	(true? (state t b)) t
	(false? (state t b)) (assoc t (get-var b) :inconsistent)
	(= (state t b) :inconsistent) t 
	:else (assoc-truth-value t b true)))
    :else table))

(defn assoc-if-consistent [table [a b :as rule]]
  (cond
   (true? (state table a))
     (cond
      (true? (state table b)) table
      (false? (state table b)) table
      (= (state table b) :inconsistent) table  
      :else (assoc-truth-value table b true))
   (nil? (state table a))
     (let [t (assoc-truth-value table a true)]
       (cond
	(true? (state t b)) t
	(false? (state t b)) table
	(= (state t b) :inconsistent) t 
	:else (assoc-truth-value t b true)))
    :else table))

(defn consistency-table
  ([rule rule-set]
     (consistency-table rule rule-set (assoc-state {} rule)))
  ([rule rule-set truth-table]
     (let [[a b] rule]
       (loop [t truth-table
	      rules rule-set
	      unapplied-rules []]
	 (if (seq rules)
	   (let [r (first rules)
		 new-t (if (= rule r) t (assoc-state t r))]
	     (if (> (count new-t) (count t))
	       (recur new-t (concat unapplied-rules (rest rules)) unapplied-rules)
	       (recur new-t (rest rules) (conj unapplied-rules r))))
	   t)))))

(defn consistent?
  ([rule rule-set]
     (not ((set (vals (consistency-table rule rule-set))) :inconsistent)))
  ([rule rule-set truth-table]
     (not ((set (vals (consistency-table rule rule-set truth-table))) :inconsistent))))

(defn partition-consistent [rule-set]
  (let [f (fn [rule-set] (set (filter #(consistent? % rule-set) rule-set)))]
    (loop [parts [] rules rule-set]
     (if (seq rules)
       (let [new-part (f rules)]
	 (recur (conj parts new-part)
		(apply clojure.set/difference rule-set new-part parts)))
       parts))))

(defn apply-priorities [partitions]
  (apply merge (for [i (range (count partitions))]
		 (zipmap (get partitions i) (repeat (count (get partitions i)) i)))))

(defn extract-vars [rule-set]
  (set (mapcat (fn [r] (map get-var r)) rule-set)))

(defn make-truth-table [rule-set]
  (let [vars (extract-vars rule-set)
	truth-vals (comb/selections [true false] (count vars))]
    (map #(zipmap vars %) truth-vals)))

(defn filter-entries [truth-table truth-values]
  (filter #(= truth-values (select-keys % (keys truth-values))) truth-table))

(defn find-conflicts [models rule]
  (let [truth-values (zipmap rule [true false])]
    (filter-entries models truth-values)))

(defn conflict? [[a b :as rule] model]
  (let [t (reduce #(assoc-state %1 %2 true) model rule)]
    (not (and (true? (t a)) (true? (t b))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def rules #{[:b :f]
	     [:p :b]
	     [:p [:not :f]]
	     [:b :w]
	     [:f :a]})

;; examples
