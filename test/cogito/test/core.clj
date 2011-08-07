(ns cogito.test.core
  (:use [cogito.core])
  (:use [clojure.test]))

(def ex-rules #{[:b :f]
		[:p :b]
		[:p [:not :f]]
		[:b :w]
		[:f :a]})

(deftest append-rule-test
  (is (append-rule ex-rules [:b :f])
      {:a true, :w true, :f true, :b true})
  (is (append-rule ex-rules [:p :b])
      {:w true, :f :inconsistent, :b true, :p true})
  (is (append-rule ex-rules [:p [:not :f]])
      {:w true, :b true, :f :inconsistent, :p true}))

(deftest tolerate?-test
  (is (true? (tolerate? ex-rules [:b :f])))
  (is (false? (tolerate? ex-rules [:p :b])))
  (is (false? (tolerate? ex-rules [:p [:not :f]]))))

(def partitions (partition-by-consistency ex-rules))

(deftest partition-by-consistency-test
  (is partitions
      [#{[:b :f] [:b :w] [:f :a]} #{[:p :b] [:p [:not :f]]}]))

(deftest z-plus-order-test
  (is (apply z-plus-order partitions)
      {[:p :b] [[:b :f]], [:p [:not :f]] [[:b :f]]}))
