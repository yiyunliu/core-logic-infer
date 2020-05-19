(ns cmsc838-final.core
  (:refer-clojure :exclude [==])
  (:use clojure.core.logic)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.match :refer [match]])
  (:require [clojure.core.logic.nominal :as nom])
  (:gen-class))

(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))

(declare typeo)

;; syntax for our terms
;; keeps track of the # of lambdas
(defne termo [e]
  ([['v i]] ) ;; not necessary to check i is nat in this case
  ([['λ ?e]]
   (fresh [?body]
     (nom/fresh [x]
       (== ?e (nom/tie x ?body))
       (termo ?body))))
  ([['λ ?A ?e]] (typeo ?A)
   (typeo ?A)
   (fresh [?body]
     (nom/fresh [x]
       (== ?e (nom/tie x ?body))
       (termo ?body))))
  ([['ap e0 e1]]
   (termo e0)
   (termo e1))
  (['true])
  (['false]))

;; fst
;; (run 1 [q] (nom/fresh [x y] (termo ['λ (nom/tie x ['λ (nom/tie y ['v x])])])))

;; snd
;; (run 1 [q] (nom/fresh [x y] (termo ['λ (nom/tie x ['λ (nom/tie y ['v y])])])))

;; id
;; (run 1 [q] (nom/fresh [y] (termo ['λ (nom/tie y ['v y])])))


(defne typeo [t]
  ([['v ?i]])
  ([[?t0 '-> ?t1]] (typeo ?t0) (typeo ?t1))
  ([['∏ ?t]]
   (fresh [?body]
     (nom/fresh [x]
       (== ?t (nom/tie x ?body))
       (typeo ?body))))
  (['bool]))

;; fst
;; (run 1 [q] (nom/fresh [x y] (typeo ['∏ (nom/tie x ['∏ (nom/tie y [['v x] '-> [['v y] '-> ['v x]]])])])))


(defne monotypeo [t]
  ([['v ?i]])
  ([[?t0 '-> ?t1]] (monotypeo ?t0) (monotypeo ?t1))  
  (['bool]))


;; List (var,type)
(defne typing-contexto [ctx]
  ([[]])
  ([[[x t] . ?ctx ]]
   (typeo t)
   (typing-contexto ?ctx)))

;; context lookup
;; disequality constraint is unnecessary
;; since nom ensures barendrecht convention
(defn lookupo [x A ctx]
  (membero [x A] ctx))

;; List type
(defne application-contexto [ctx]
  ([[]])
  ([[?t . ?ctx]] (typeo ?t) (application-contexto ?ctx)))

;; this is what happens when you host your language on JVM
(declare subtypingo)
(declare application-subtypingo)



(defne map-fsto [ctx ctxo]
  ([[] []])
  ([[[?a ?b] . ?ctx] _]
   (fresh (?ctxo)
     (conso ?a ?ctxo ctxo)
     (map-fsto ?ctx ?ctxo))))

(defne not-membero [x xs]
  ([_ []])
  ([_ [?x . ?xs]]
   (!= ?x x)
   (not-membero x ?xs)))

(defne map-sndo [ctx ctxo]
  ([[] []])
  ([[[?a ?b] . ?ctx] _]
   (fresh (?ctxo)
     (conso ?b ?ctxo ctxo)
     (map-sndo ?ctx ?ctxo))))

;; i think it's more efficient to construct a list
;; and check x \in list than checking x \in t
;; everytime
(defne type-fvo [t tvs]
  ([['v ?i] [?i]])
  ([['∏ ?t]]
   (fresh [?body]
     (nom/fresh [x]
       (== ?t (nom/tie x ?body))
       (type-fvo ?body tvs))))
  ([[?t0 '-> ?t1] ?tvs]
   (fresh [?tvs0 ?tvs1]
     (type-fvo ?t0 ?tvs0)
     (type-fvo ?t1 ?tvs1)
     (appendo ?tvs0 ?tvs1 ?tvs)))
  (['bool []]))

;; name capture is avoided as one would expect
;; (run 1 [q] (nom/fresh [x y]
;;              (fresh [tvs]
;;                (type-fvo ['∏ (nom/tie x ['∏ (nom/tie y [['v x] '-> [['v y] '-> ['v x]]])])] tvs)
;;                (membero x tvs))))

(defne ctx-fvo [ll lout]
  ([[] []])
  ([[[_ ?x] . ?l1] _]
   (fresh [?fvs ?lout]
     (type-fvo ?x ?fvs)
     (appendo ?fvs ?lout lout)
     (ctx-fvo ?l1 ?lout))))

(defne bind-with-fvso [A-fvs ctx-fvs A A-out]
  ([ [] _ A A])
  ([ [x . xs] _ A _]
   (nom/hash x ctx-fvs)
   (nom/hash x xs)
   (bind-with-fvso xs ctx-fvs ['∏ (nom/tie x A)] A-out))
  ([ [x . xs] _ A _]
   (conde
    ((membero x xs))
    ((membero x ctx-fvs)))
   (bind-with-fvso xs ctx-fvs A A-out)))

(defn t-geno [ctx A A-generalized]
  (fresh [A-fvs ctx-fvs]
    (ctx-fvo ctx ctx-fvs)
    (type-fvo A A-fvs)
    (bind-with-fvso A-fvs ctx-fvs A A-generalized)))


;; ok. nom/hash works as expected
(run 1 [q] (nom/fresh [x y]
             (type-fvo [['v x] '-> [['v y] '-> ['v x]]] q)
             (fresh [z zs]
               (conso z zs q)
               (nom/hash x zs))))

;; ok. type properly generalized under the empty context
(run 1 [q] (nom/fresh [x y]
             (fresh [tvs]
               (t-geno [] [['v x] '-> [['v y] '-> ['v x]]] q))))


;; ok. type properly generalized when context is non-empty
(run 1 [q] (nom/fresh [x y v]
             (fresh [tvs]
               (t-geno [[v ['v x]]] [['v x] '-> [['v y] '-> ['v x]]] q))))


(defne typing-state-o [ctx actx e B]
  
  ;; t-int
  ([gen gen _ [] _ 'bool]
   (boolo e))
  
  ;; t-lam
  ([_ _ ctx [?A .  ?actx] ['λ ?e] [?A '-> ?B]]
   ;; fail
   (fresh [x _ ?e-opened]
     (== x ['S gen])
     (term-openo x ?e ?e-opened)
     (typing-state-o x gen-out (llist [x ?A] ctx) ?actx ?e-opened ?B)))


  ;; t-lam2
  ([_ _ ctx [] ['λ ?e] [?t '-> ?B]]
   (fresh [x ?e-opened]
     ;; (== ?B ?e)
     ;; (== B [x gen-out (llist [x ?t] ctx) actx ?e-opened ?B])
     (== x ['S gen])
     (term-openo x ?e ?e-opened)
     (typing-state-o x gen-out (llist [x ?t] ctx) actx ?e-opened ?B)
     (monotypeo ?t)
     ))

  ;; t-lamann1
  ([_ _ ctx [?C . ?actx] ['λ ?A ?e] [?C '-> ?B]]
   (fresh [x ?gen-out ?e-opened]
     (== x ['S gen])
     (closed-typeo ?A)
     (term-openo x ?e ?e-opened)
     (subtypingo gen ?gen-out ?C ?A)     
     (typing-state-o ?gen-out gen-out (llist [x ?A] ctx) ?actx ?e-opened ?B)))

  ;; t-lamann2
  ([_ _ ctx [] ['λ ?A ?e] [?A '-> ?B]]
   (fresh [x ?e-opened]
     (== x ['S gen])
     (closed-typeo ?A)
     (term-openo x ?e ?e-opened)
     (typing-state-o x gen-out (llist [x ?A] ctx) actx ?e-opened ?B)))

  ;; t-gen is pulled out

  ;; t-app
  ([_ _ ctx actx ['ap ?e1 ?e2] ?C]
   (fresh [?A ?B ?gen-out0 ?actx]
     (typing-state-o gen ?gen-out0 ctx [] ?e2 ?A)
     (t-geno ctx ?A ?B)
     (conso ?B actx ?actx)
     (typing-state-o ?gen-out0 gen-out ctx ?actx ?e1 [?B '-> ?C])))
  ;; t-var
  ([_ _ _ _ ['fv x] B]
   (fresh [A]
     (lookupo x A ctx)
     (application-subtypingo gen gen-out actx A B))))

(defne subtypingo [gen gen-out t0 t1]
  ;; s-forallr
  ([_ _ ?A ['∏ ?B]]
   (fresh [?new-gen ?B-opened ?fvs]
     (== ?new-gen ['S gen])
     (type-openo ?new-gen ?B ?B-opened)
     (type-fvo ?B ?fvs)
     (not-membero ?new-gen ?fvs)
     (subtypingo ?new-gen gen-out ?A ?B-opened)))

  ;; s-foralll
  ([_ _ ['∏ ?A] ?B]
   (fresh [?t ?A-opened]
     (type-sub-openo ?t ?A ?A-opened)
     (monotypeo ?t)
     (subtypingo gen gen-out ?A-opened ?B)))

  ;; s-fun
  ([_ _ [?A '-> ?B] [?C '-> ?D]]
   (fresh [?gen-out]
     (subtypingo gen ?gen-out ?C ?A)
     (subtypingo ?gen-out gen-out ?B ?D)))

  ;; s-var
  ([gen gen ['fv ?x] ['fv ?x]])

  ;; s-bool
  ([gen gen 'bool 'bool]))

(defne application-subtypingo [gen gen-out actx t0 t1]
  ;; s-foralll2
  ([_ _ [?C . ?actx] ['∏ ?A] ?B]
   (fresh [?t ?A-opened]
     (monotypeo ?t)
     (type-sub-openo ?t ?A ?A-opened)
     (application-subtypingo gen gen-out actx ?A-opened ?B)))

  ;; s-sfun2
  ([_ _ [?C . ?actx] [?A '-> ?B] [?C '-> ?D]]
   (fresh [?gen-out]
     (subtypingo gen ?gen-out ?C ?A)
     (application-subtypingo ?gen-out gen-out ?actx ?B ?D)))

  ;; s-empty
  ([gen gen [] t0 t0]))

(defn typingo [ctx actx e B]
  (fresh [gen-out]
    (typing-state-o 'Z gen-out ctx actx ['ap term-id e] B)))


(defn infer-with-ctx-n [n ctx actx t]
  (run n [q] (typingo ctx actx t q) ))

(defn infer-with-ctx-1 [ctx actx t]
  (infer-with-ctx-n 1))

(defn synth-1 [t]
  (run 1 [q] (typingo [] [] q t) (termo q)))

;; (run 1 [q] (typingo [['x 'bool]] [] ['fv 'x] q))

;; (infer-with-ctx-n 2 [] [] '[λ [bv Z]])

;; (run 1 [q] (typingo ['(x (∏ ([bv Z] -> [bv Z])))] [] ['ap ['fv 'x] true]  q))

;; (synth-1 '(∏ ([bv Z] -> [bv Z])))



