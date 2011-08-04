(ns cogito.core)

(defn bool? [x] (= (type x) java.lang.Boolean))

(defn negate? [x]
  (and (vector? x) (= (first x) :not)))

(defn state [table x]
  (if (negate? x)
    (not (table (second x)))
    (table x)))

(defn set-state [table x p]
  (if (negate? x)
    (assoc table (second x) (not p))
    (assoc table x p)))

(defn get-var [x]
  (if (negate? x)
    (second x)
    x))

(defn consistency-table [rule rule-set]
  (let [[_ a b] rule
	truth-table (reduce #(set-state %1 %2 true) {} (rest rule))
	f (fn [table [_ ai bi :as r]]
	    (if (= rule r)
	      table
	      (if (true? (state table ai))
	         (cond
		  (true? (state table bi))
		    table
		  (false? (state table bi))
		    (assoc table (get-var bi) :inconsistent)
		  (= (state table bi) :inconsistent)
		    table  
		  :else
		    (set-state table bi true))
		 table)))]
    (loop [t truth-table
	   rules rule-set
	   unapplied-rules []]
      (if (seq rules)
	(let [new-t (f t (first rules))]
	  (if (> (count new-t) (count t))
	    (recur new-t (concat unapplied-rules (rest rules)) unapplied-rules)
	    (recur new-t (rest rules) (conj unapplied-rules (first rules)))))
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

(def omega [[:-> :b :f]
	    [:-> :p :b]
	    [:-> :p [:not :f]]
	    [:-> :b :w]
	    [:-> :f :a]])

(def omega3 #{[:-> :b :f]
	     [:-> :p :b]
	     [:-> :p [:not :f]]
	     [:-> :b :w]
	     [:-> :f :a]})

;; examples
(consistency-table [:-> :b :f] omega3)
(consistent? [:-> :b :f] omega3)
;; b ^ f ^ p => b ^ p => [not f] ^ b => w ^ f => a
;; t   t                           t    t   t    t

(consistency-table [:-> :p :b] omega3)
(consistent? [:-> :p :b] omega3)
;; p ^ b ^ b => f ^ p => [not f] ^ b => w ^ f => a
;; t   t   t    t   t      x       t    t   t    t

(consistency-table [:-> :p [:not :f]] omega3)
(consistent? [:-> :p [:not :f]] omega3)


(partition-consistent omega3)

(apply-priorities (partition-consistent omega3))

(clojure.set/difference omega3 (partition-consistent omega3))