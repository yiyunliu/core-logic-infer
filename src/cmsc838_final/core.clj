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


(defne typingo [ctx actx e B]
  
  ;; t-bool
  ([_ [] _ 'bool]
   (boolo e))
  
  ;; t-lam
  ([ctx [?A .  ?actx] _ [?A '-> ?B]]
   (nom/fresh [x]
     (fresh [?body]
       (== e ['λ (nom/tie x ?body)])
       (typingo (llist [x ?A] ctx) ?actx ?body ?B))))


  ;; t-lam2
  ([ctx [] _ [?t '-> ?B]]
   (nom/fresh [x]
     (monotypeo ?t)
     (fresh [?body]
       (== e ['λ (nom/tie x ?body)])
       (typingo (llist [x ?t] ctx) actx ?body ?B))))

  ;; t-lamann1
  ([ctx [?C . ?actx] _ [?C '-> ?B]]
   (nom/fresh [x]
     (fresh [?body ?A]
       (== e ['λ ?A (nom/tie x ?body)])
       (subtypingo ?C ?A)
       (typingo (llist [x ?A] ctx) ?actx ?body ?B))))

  ;; t-lamann2
  ([ctx [] _ [?A '-> ?B]]
   (nom/fresh [x]
     (fresh [?body ?A]
       (== e ['λ ?A (nom/tie x ?body)])
       (typingo (llist [x ?A] ctx) actx ?body ?B))))

  ;; t-gen is pulled out

  ;; t-app
  ([ctx actx ['ap ?e1 ?e2] ?C]
   (fresh [?A ?B]
     (typingo ctx [] ?e2 ?A)
     (t-geno ctx ?A ?B)
     (typingo ctx (llist ?B actx) ?e1 [?B '-> ?C])))

  ;; t-var
  ([_ _ ['fv x] B]
   (fresh [A]
     (lookupo x A ctx)
     (application-subtypingo actx A B))))

(defne subtypingo [t0 t1]
  ;; s-forallr
  ([_ _]
   (nom/fresh [x]
     (fresh [?body]
       (== t1 ['∏ (nom/tie x ?body)])
       (nom/hash x t0)
       (subtypingo t0 ?body))))

  ;; s-foralll
  ([_ _]
   (nom/fresh [x]
     (fresh [?t ?body]
       (== t0 ['∏ (nom/tie x ?body)])
       (monotypeo ?t)
       (subtypingo ?body t1))))

  ;; s-fun
  ([[?A '-> ?B] [?C '-> ?D]]
   (subtypingo ?C ?A)
   (subtypingo ?B ?D))

  ;; s-var
  ([['fv ?x] ['fv ?x]])

  ;; s-bool
  (['bool 'bool]))

(defne application-subtypingo [actx t0 t1]
  ;; s-foralll2
  ([[?C . ?actx] _ _]
   (nom/fresh [x]
     (fresh [?t ?body]
       (== t0 ['∏ (nom/tie x ?body)])
       (monotypeo ?t)
       (application-subtypingo actx ?body t1))))

  ;; s-sfun2
  ([[?C . ?actx] [?A '-> ?B] [?C '-> ?D]]
   (subtypingo ?C ?A)
   (application-subtypingo ?actx ?B ?D))

  ;; s-empty
  ([[] t0 t0]))


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



