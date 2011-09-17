(ns cogito.atms.unify)

(defn variable? 
  "A keword whose first character is ?

Examples:

    (variable? :x)
    (variable? :?x)
    (variable? 1)
    (variable? '?x)
    (variable? 'x)
"
  ([x]
     (and (or (symbol? x) (keyword? x)) (= (first (name x)) \?))))

(defn free-in? 
  "
Returns nil if <var> occurs in <exp>, assuming <bindings>

Examples:

    (free-in? :?x :y {:?x [:a 1], :?y 2, :?a 3})
    (free-in? :?x :x {:?x [:a 1], :?y 2, :?a 3})
    (free-in? :?x [:?x 1] {:?x [:?a 1], :?y 2, :?a 3})
"
([var exp bindings]
   (cond
    (nil? exp) true
    (= var exp) nil
    (variable? exp) (if-let [val (bindings exp)]
		      (free-in? var val bindings)
		      true)
    (not (coll? exp)) true
    (free-in? var (first exp) bindings)
    (free-in? var (rest exp) bindings))))

(declare unify)

(defn unify-variable
  ""
  ([var exp bindings]
     (cond
      ;; Must distinguish no value from value of nil
      (get (set (keys bindings)) var)
        (unify (bindings var) exp bindings)
      ;; if safe, bind <var> to <exp>
      (free-in? var exp bindings)
	(assoc bindings var exp)
      :else :FAIL)))

(defn unify
  "
Examples:

    (unify :?x [:?y] {})
"
  ([a b & bindings]
     (let [bindings (apply hash-map bindings)]
       (cond
	(= a b) bindings
	(variable? a) (unify-variable a b bindings)
	(variable? b) (unify-variable b a bindings)
	(or (not (coll? a)) (not (coll? b))) :FAIL
	:else (let [new-bindings (unify (first a) (first b) bindings)]
		(if (not= :FAIL new-bindings)
		  (unify (rest a) (rest b) new-bindings)
		  :FAIL))))))

