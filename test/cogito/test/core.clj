(ns cogito.test.core
  (:use [cogito.core])
  (:use [clojure.test]))

(def ex-rules #{[:b :f]
		[:p :b]
		[:p [:not :f]]
		[:b :w]
		[:f :a]})

(deftest append-rule-test
  (is (= (append-rule ex-rules [:b :f])
	 {:a true, :w true, :f true, :b true}))
  (is (= (append-rule ex-rules [:p :b])
	 {:w true, :f :inconsistent, :b true, :p true}))
  (is (= (append-rule ex-rules [:p [:not :f]])
	 {:w true, :b true, :f :inconsistent, :p true})))

(deftest tolerate?-test
  (is (true? (tolerate? ex-rules [:b :f])))
  (is (false? (tolerate? ex-rules [:p :b])))
  (is (false? (tolerate? ex-rules [:p [:not :f]]))))

(def partitions (partition-by-consistency ex-rules))

(deftest partition-by-consistency-test
  (is (= partitions
	 [#{[:b :f] [:b :w] [:f :a]} #{[:p :b] [:p [:not :f]]}])))

(def z-ordered-rules (apply z-plus-order partitions))

(deftest z-plus-order-test
  (is (= z-ordered-rules
	 {[:p :b] [[:b :f]], [:p [:not :f]] [[:b :f]]})))

(def rules-map {[:b :f] 1
		[:p :b] 1
		[:p [:not :f]] 1
		[:b :w] 1
		[:f :a] 1})

(def z-ordered-rules-map (apply-scores rules-map z-ordered-rules))

(deftest apply-scores-test
  (is (= z-ordered-rules-map
	 {[:b :f] 1, [:p :b] 3, [:p [:not :f]] 3, [:b :w] 1, [:f :a] 1})))


(deftest score-query-test
  ;; penguins ^ birds -> fly
  (is (= (score-query (process-query z-ordered-rules-map {:p true, :b true, :f true})) 3))
  (is (= (score-query (process-query z-ordered-rules-map {:p true, :b true, :f false})) 1))
  
  ;; birds -> penguins
  (is (= (score-query (process-query z-ordered-rules-map {:b true, :p true})) 1))
  (is (= (score-query (process-query z-ordered-rules-map {:b true, :p false})) 0))
  
  ;; red ^ birds -> fly
  (is (= (score-query (process-query z-ordered-rules-map {:r true, :b true, :f true})) 0))
  (is (= (score-query (process-query z-ordered-rules-map {:r true, :b true, :f false})) 1))

  ;; birds -> airborn
  (is (= (score-query (process-query z-ordered-rules-map {:b true, :a true})) 0))
  (is (= (score-query (process-query z-ordered-rules-map {:b true, :a false})) 1)) 
  
  ;; undecided
  (is (= (score-query (process-query z-ordered-rules-map {:p true, :w true})) 1))
  (is (= (score-query (process-query z-ordered-rules-map {:p true, :w false})) 1)))


(deftest query-test
  ;; penguins ^ birds -> fly
  (is (= (query rules-map
	      {:p true, :b true, :f true}
	      {:p true, :b true, :f false})
	 {{:p true, :b true, :f true} 3
	  {:p true, :b true, :f false} 1}))
  
  ;; birds -> penguins
  (is (= (query rules-map
	      {:b true, :p true}
	      {:b true, :p false})
	 {{:b true, :p true} 1
	  {:b true, :p false} 0}))
  
  ;; red ^ birds -> fly
  (is (= (query rules-map
	      {:r true, :b true, :f true}
	      {:r true, :b true, :f false})
	 {{:r true, :b true, :f true} 0
	  {:r true, :b true, :f false} 1}))

  ;; birds -> airborn
  (is (= (query rules-map
	      {:b true, :a true}
	      {:b true, :a false})
	 {{:b true, :a true} 0
	  {:b true, :a false} 1}))
  
  ;; undecided
  (is (= (query rules-map
	      {:p true, :w true}
	      {:p true, :w false})
	 {{:p true, :w true} 1
	  {:p true, :w false} 1})))

(deftest entailed-test

    (is (= (entailed rules-map ($and :p :b) :f)
	   {{:b true, :p true, :f true} 3, {:f false, :p true, :b true} 1}))

    (is (= (entailed rules-map :b ($not :p))
	   {{:p true, :b true} 1, {:b true, :p false} 0}))

    (is (= (entailed rules-map ($and :r :b) :f)
	   {{:b true, :r true, :f true} 0, {:f false, :r true, :b true} 1}))

    (is (= (entailed rules-map :b :a)
	   {{:a false, :b true} 1, {:b true, :a true} 0}))

    (is (= (entailed rules-map :p :w)
	   {{:w false, :p true} 1, {:p true, :w true} 1}))

    (is (= (entailed rules-map ($or :b :p) :f)
	   {{:p true, :b true, :f true} 3,
	    {:p false, :b true, :f true} 0,
	    {:f false, :b true, :p true} 1,
	    {:p true, :b false, :f true} 3,
	    {:f false, :b true, :p false} 1,
	    {:f false, :b false, :p true} 3})))


(deftest entailed?-test
  (is (false? (entailed? rules-map ($and :p :b) :f))) 
  (is (true? (entailed? rules-map :b ($not :p)))) 
  (is (true? (entailed? rules-map ($and :r :b) :f)))
  (is (true? (entailed? rules-map :b :a)))
  (is (nil? (entailed? rules-map :p :w)))
  (is (true? (entailed? rules-map ($or :b :p) :f))))

(deftest stmt-to-models-test
  (is (= (stmt-to-models [:not :a]) ($not :a)))
  (is (= (stmt-to-models [:and :a :b]) ($and :a :b)))
  (is (= (stmt-to-models [:or :a :b]) ($or :a :b)))
  (is (= (stmt-to-models [:=> :a :b]) ($=> :a :b)))
  (is (= (stmt-to-models [:and [:not :a] :b]) ($and ($not :a) :b)))
  (is (= (stmt-to-models [:or [:not :a] :b]) ($or ($not :a) :b)))
  (is (= (stmt-to-models [:or [:and :a :b] [:and :c :d]]) ($or ($and :a :b) ($and :c :d)))))