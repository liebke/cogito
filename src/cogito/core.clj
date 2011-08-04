(ns cogito.core)

(defn bool? [x] (= (type x) java.lang.Boolean))

(defn negated?? [x]
  (and (vector? x) (= (first x) :not)))
ass
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

(defn assoc-if-consistent [table [ai bi :as r]]
  (if (true? (state table ai))
     (cond
      (true? (state table bi)) table
      (false? (state table bi))
        (assoc table (get-var bi) :inconsistent)
      (= (state table bi) :inconsistent) table  
      :else (assoc-state table bi true))
    table))

(defn consistency-table [rule rule-set]
  (let [[a b] rule
	truth-table (reduce #(assoc-state %1 %2 true) {} rule)]
    (loop [t truth-table
	   rules rule-set
	   unapplied-rules []]
      (if (seq rules)
	(let [r (first rules)
	      new-t (if (= rule r) t (assoc-if-consistent t r))]
	  (if (> (count new-t) (count t))
	    (recur new-t (concat unapplied-rules (rest rules)) unapplied-rules)
	    (recur new-t (rest rules) (conj unapplied-rules r))))
	t))))

(defn consistent? [rule rule-set]
  (not ((set (vals (consistency-table rule rule-set))) :inconsistent)))

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

(def rules #{[:b :f]
	     [:p :b]
	     [:p [:not :f]]
	     [:b :w]
	     [:f :a]})

;; examples
(consistency-table [:b :f] rules)
(consistent? [:b :f] rules)
;; b ^ f ^ p => b ^ p => [not f] ^ b => w ^ f => a
;; t   t                           t    t   t    t

(consistency-table [:p :b] rules)
(consistent? [:p :b] rules)
;; p ^ b ^ b => f ^ p => [not f] ^ b => w ^ f => a
;; t   t   t    t   t      x       t    t   t    t

(consistency-table [:p [:not :f]] rules)
(consistent? [:p [:not :f]] rules)


(partition-consistent rules)

(apply-priorities (partition-consistent rules))

