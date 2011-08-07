(ns cogito.test.core
  (:use [cogito.core])
  (:use [clojure.test]))

(def ex-rules #{[:b :f]
		[:p :b]
		[:p [:not :f]]
		[:b :w]
		[:f :a]})

(deftest append-rule-test
  (is (append-rule [:b :f] ex-rules)
      {:a true, :w true, :f true, :b true})
  (is (append-rule [:p :b] ex-rules)
      {:w true, :f :inconsistent, :b true, :p true})
  (is (append-rule [:p [:not :f]] ex-rules)
      {:w true, :b true, :f :inconsistent, :p true}))

(deftest tolerate?-test
  (is (true? (tolerate? [:b :f] ex-rules)))
  (is (false? (tolerate? [:p :b] ex-rules)))
  (is (false? (tolerate? [:p [:not :f]] ex-rules))))

(def partitions (partition-by-consistency ex-rules))

(deftest partition-by-consistency-test
  (is partitions
      [#{[:b :f] [:b :w] [:f :a]} #{[:p :b] [:p [:not :f]]}]))

(deftest priorities-test
  (is (apply-priorities partitions)
      {[:p :b] 1, [:p [:not :f]] 1, [:f :a] 0, [:b :w] 0, [:b :f] 0}))

(deftest z-plus-order-test
  (is (apply z-plus-order partitions)
      {[:p :b] [[:b :f]], [:p [:not :f]] [[:b :f]]}))
