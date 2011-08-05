(ns cogito.test.core
  (:use [cogito.core])
  (:use [clojure.test]))

(def ex-rules #{[:b :f]
	     [:p :b]
	     [:p [:not :f]]
	     [:b :w]
	     [:f :a]})

(deftest consistency-map-test
  (is (consistency-table [:b :f] ex-rules)
      {:a true, :w true, :f true, :b true})
  (is (consistency-table [:p :b] ex-rules)
      {:w true, :f :inconsistent, :b true, :p true})
  (is (consistency-table [:p [:not :f]] ex-rules)
      {:w true, :b true, :f :inconsistent, :p true}))

(deftest consistency?-test
  (is (true? (consistent? [:b :f] ex-rules)))
  (is (false? (consistent? [:p :b] ex-rules)))
  (is (false? (consistent? [:p [:not :f]] ex-rules))))

(deftest partition-consistent-test
  (is (partition-consistent rules)
      [#{[:b :f] [:b :w] [:f :a]} #{[:p :b] [:p [:not :f]]}]))

(deftest priorities-test
  (is (apply-priorities (partition-consistent rules))
      {[:p :b] 1, [:p [:not :f]] 1, [:f :a] 0, [:b :w] 0, [:b :f] 0}))
