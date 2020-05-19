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

(defn nat->int [x]
  (match [x]
         ['Z] 0
         [(['S y] :seq)] (+ 1 (nat->int y))))

(defn int->nat [x]
  (match [x]
         [0] 'Z
         :else (list 'S (int->nat (- x 1)))))

(defne nato [x]
  ([['S ?o]] (nato ?o))
  (['Z]))

(defne pluso [x y o]
  (['Z y y])
  ([['S ?x] _ _]
   (fresh [?o]
     (== (list 'S ?o) o)
     (pluso ?x y ?o) )))

(defn leqo [x y]
  (fresh (z)
    (pluso z x y)))

(defn lto [x y]
  (fresh (z)
    (leqo (list 'S x) y)))

(defne boolo [x]
  ([true])
  ([false]))

(def term-id
  '(λ (bv Z)))

;; (run* [q] (termo term-id))

(def term-fst
  '(λ (λ (bv (S Z)))))

;; (run* [q] (termo term-fst))

(def term-snd
  '(λ (λ (bv Z))))

;; (run* [q] (termo term-snd))

(def term-illegal
  '(λ (λ (bv (S (S Z))))))

;; (run* [q] (termo term-illegal))

(declare typeo)

;; syntax for our terms
;; keeps track of the # of lambdas
(defne term-i-o [m-i e]
  ([_ ['fv i]])
  ([_ ['bv i]] (lto i m-i)) ;; not necessary to check i is nat in this case
  ([_ ['λ ?e]] (term-i-o (list 'S m-i) ?e))
  ([_ ['λ ?A ?e]] (typeo ?A) (term-i-o (list 'S m-i) ?e))
  ([_ ['ap e0 e1]] (term-i-o m-i e0) (term-i-o m-i e1))
  ([_ _] (boolo e)))

(defn termo [e]
  (term-i-o 'Z e))

(defne closed-term-i-o [m-i e]
  ([_ ['bv i]] (lto i m-i)) ;; not necessary to check i is nat in this case
  ([_ ['λ ?e]] (closed-term-i-o (list 'S m-i) ?e))
  ([_ ['λ ?A ?e]] (typeo ?A) (closed-term-i-o (list 'S m-i) ?e))
  ([_ ['ap e0 e1]] (closed-term-i-o m-i e0) (closed-term-i-o m-i e1))
  ([_ _] (boolo e)))

(defn closed-termo [e]
  (closed-term-i-o 'Z e))


(defne type-i-o [m-i t]
  ([_ ['fv ?i]])
  ([_ [?t0 '-> ?t1]] (type-i-o m-i ?t0) (type-i-o m-i ?t1))
  ([_ ['∏ ?t]] (type-i-o (list 'S m-i) ?t))
  ([_ ['bv ?i]] (lto ?i m-i))
  ([_ 'bool]))


(defn typeo [t]
  (type-i-o 'Z t))

(defne closed-type-i-o [m-i t]
  ([_ [?t0 '-> ?t1]] (closed-type-i-o m-i ?t0) (closed-type-i-o m-i ?t1))
  ([_ ['∏ ?t]] (closed-type-i-o (list 'S m-i) ?t))
  ([_ ['bv ?i]] (lto ?i m-i))
  ([_ 'bool]))


(defn closed-typeo [t]
  (closed-type-i-o 'Z t))


(def type-fst
  '(∏ (∏ ((bv (S Z)) -> ((bv Z) -> (bv (S Z)))))))

(def type-fst-v2
  '[∏ [∏ ([bv Z] -> ([bv (S Z)] -> [bv Z]))]])

;; (run* [q] (typeo type-fst))


(def type-snd
  '(∏ (∏ ((bv (S Z)) -> ((bv Z) -> (bv Z))))))

;; (run* [q] (typeo type-snd))


(defne monotypeo [t]
  ([['fv ?i]])
  ([[?t0 '-> ?t1]] (monotypeo ?t0) (monotypeo ?t1))  
  (['bool]))




;; precondition: t is a term
(defne term-nocheck-openo [k x t t-opened]
  ;; open
  ([_ _ ['fv ?x] ['fv ?x]])
  ([_ _ ['bv k] ['fv x]])
  ([_ _ ['bv ?k] t] (!= ?k k))
  ([_ _ ['λ ?e] _] (fresh (?e-opened)
                     (== ['λ ?e-opened] t-opened)
                     (term-nocheck-openo (list 'S k) x ?e ?e-opened)))
  ([_ _ ['λ ?A ?e] _] (fresh (?e-opened)
                        (== ['λ ?A ?e-opened] t-opened)
                        (term-nocheck-openo (list 'S k) x ?e ?e-opened)))
  ([_ _ ['ap ?e0 ?e1] _] (fresh (?e0-opened ?e1-opened)
                           (== t-opened (list 'ap ?e0-opened ?e1-opened))
                           (term-nocheck-openo k x ?e0 ?e0-opened)
                           (term-nocheck-openo k x ?e1 ?e1-opened)))
  ;; bug bug bug!!
  ([_ _ _ _] (boolo t) (== t-opened t)))

(defne term-nocheck-closeo [k x t t-closed]
  ;; open
  ([_ _ ['fv x] ['bv k]])
  ([_ _ ['fv ?x] ['bv k]] (!= ?x x))
  ([_ _ ['bv _] t])
  ([_ _ ['λ ?e] _] (fresh (?e-closed)
                     (== ['λ ?e-closed] t-closed)
                     (term-nocheck-closeo ['S k] x ?e ?e-closed)))
  ([_ _ ['λ ?A ?e] _] (fresh (?e-closed)
                        (== ['λ ?A ?e-closed] t-closed)
                        (term-nocheck-closeo ['S k] x ?e ?e-closed)))
  ([_ _ ['ap ?e0 ?e1] _] (fresh (?e0-closed ?e1-closed)
                           (== t-closed (list 'ap ?e0-closed ?e1-closed))
                           (term-nocheck-closeo k x ?e0 ?e0-closed)
                           (term-nocheck-closeo k x ?e1 ?e1-closed)))
  ;; bug bug bug!!
  ([_ _ _ _] (boolo t) (== t-closed t)))


(defn term-openo [x t t-opened]
  (term-nocheck-openo 'Z x t t-opened))


;; can't be defined in terms of openo
(defn term-closeo [x t t-closed]
  (term-nocheck-closeo 'Z x t t-closed))

;; (run* [q] (term-closeo 'x  '(λ (fv x)) q))


(defne type-nocheck-openo [k x t t-opened]
  ;; open
  ([_ _ ['fv ?x] ['fv ?x]])
  ([_ _ ['bv k] ['fv x]])
  ([_ _ ['bv ?k] t] (!= ?k k))
  ([_ _ ['∏ ?e] _] (fresh (?e-opened)
                     (== ['∏ ?e-opened] t-opened)
                     (type-nocheck-openo (list 'S k) x ?e ?e-opened)))
  ([_ _ [?e0 '-> ?e1] _] (fresh (?e0-opened ?e1-opened)
                           (== t-opened (list ?e0-opened '-> ?e1-opened))
                           (type-nocheck-openo k x ?e0 ?e0-opened)
                           (type-nocheck-openo k x ?e1 ?e1-opened)))
  ;; bug bug bug!!
  ([_ _ 'bool 'bool]))


(defne type-nocheck-sub-openo [k x t t-opened]
  ;; open
  ([_ _ ['bv k] x])
  ([_ _ ['bv ?k] t] (!= ?k k))
  ([_ _ ['fv ?x] ['fv ?x]])
  ([_ _ ['∏ ?e] _] (fresh (?e-opened)
                     (== ['∏ ?e-opened] t-opened)
                     (type-nocheck-sub-openo (list 'S k) x ?e ?e-opened)))
  ([_ _ [?e0 '-> ?e1] _] (fresh (?e0-opened ?e1-opened)
                           (== t-opened (list ?e0-opened '-> ?e1-opened))
                           (type-nocheck-sub-openo k x ?e0 ?e0-opened)
                           (type-nocheck-sub-openo k x ?e1 ?e1-opened)))
  ;; bug bug bug!!
  ([_ _ 'bool 'bool]))

(defn type-sub-openo [x t t-opened]
  (type-nocheck-sub-openo 'Z x t t-opened))

(defne type-nocheck-closeo [k x t t-closed]
  ;; open
  ([_ x ['fv x] ['bv k]] )
  ([_ _ ['bv ?k] t])
  ([_ _ ['fv ?x] t] (!= ?x x))
  ([_ _ ['∏ ?e] _] (fresh (?e-closed)
                     (== ['∏ ?e-closed] t-closed)
                     (type-nocheck-closeo (list 'S k) x ?e ?e-closed)))
  ([_ _ [?e0 '-> ?e1] _] (fresh (?e0-closed ?e1-closed)
                           (== t-closed (list ?e0-closed '-> ?e1-closed))
                           (type-nocheck-closeo k x ?e0 ?e0-closed)
                           (type-nocheck-closeo k x ?e1 ?e1-closed)))
  ;; bug bug bug!!
  ([_ _ _ _] (boolo t) (== t-closed t)))


(defn type-openo [x t t-opened]
  (type-nocheck-openo 'Z x t t-opened))


;; can't be defined in types of openo
(defn type-closeo [x t t-closed]
  (type-nocheck-closeo 'Z x t t-closed))


;; List (var,type)
(defne typing-contexto [ctx]
  ([[]])
  ([[[x t] . ?ctx ]]
   (typeo t)
   (typing-contexto ?ctx)))

;; List type
(defne application-contexto [ctx]
  ([[]])
  ([[?t . ?ctx]] (typeo ?t) (application-contexto ?ctx)))

;; this is what happens when you host your language on JVM
(declare subtypingo)
(declare application-subtypingo)

;; assoc list lookup
;; disequality constraint is unnecessary
;; since we use the barendrecht convention
(defn lookupo [x A ctx]
  (membero [x A] ctx))

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

(defne type-fvo [t tvs]
  ([['fv ?i] [?i]])
  ([['∏ ?t] _] (type-fvo ?t tvs))
  ([[?t0 '-> ?t1] ?tvs]
   (fresh [?tvs0 ?tvs1]
     (type-fvo ?t0 ?tvs0)
     (type-fvo ?t1 ?tvs1)
     (appendo ?tvs0 ?tvs1 ?tvs)))
  ([['bv _] []])
  (['bool []]))

(defne term-fvo [e fvs]
  ([['bv i] []])
  ([['fv i] [i]]) ;; not necessary to check i is nat in this case
  ([['λ ?e] _] (term-fvo ?e fvs))
  ([['λ _ ?e] _] (term-fvo ?e fvs))
  ([['ap e0 e1] _] (fresh [fvs0 fvs1]
                     (term-fvo e0 fvs0)
                     (term-fvo e1 fvs1)
                     (appendo fvs0 fvs1 fvs)))
  ([_ _] (boolo e) (== fvs [])))

(defne rem-allo [x xs ys]
  ([_ [] []])
  ([x [x . ?xs] ?ys]
   (rem-allo x ?xs ?ys))
  ([x [?x . ?xs] [?x . ?ys]]
   (!= x ?x)
   (rem-allo x ?xs ?ys)))

(defne differenceo [l0 l1 ld]
  ([ _ [] l0])
  ([ _ [?x . ?l1] ?l2]
   (fresh [?l0]
     (rem-allo ?x l0 ?l0)
     (differenceo ?l0 ?l1 ?l2))))

(defne ctx-fvo [ll lout]
  ([[] []])
  ([[[_ ?x] . ?l1] _]
   (fresh [?fvs ?lout]
     (type-fvo ?x ?fvs)
     (appendo ?fvs ?lout lout)
     (ctx-fvo ?l1 ?lout))))

(defne close-with-fvarso [vars A A-generalized]
  ([[] A A])
  ([[?v . ?vars] _ _]
   (fresh [B]
     (type-closeo ?v A B)
     (close-with-fvarso ?vars ['∏ B] A-generalized))))

(def type-fst-fv
  '((fv x) -> ((fv y) -> (fv x))))

(defne dedupo [xs ys]
  ([[] []])
  ([[?x . ?xs] [?x . ?zs]]
   (fresh [?ys]
     (rem-allo ?x ?xs ?ys)
     (dedupo ?ys ?zs))))

(defn t-geno [ctx A A-generalized]
  (fresh [A-fvars ctx-fvars A-ctx-diff diff-deduped]
    (ctx-fvo ctx ctx-fvars)
    (type-fvo A A-fvars)
    (differenceo A-fvars ctx-fvars A-ctx-diff)
    (dedupo A-ctx-diff diff-deduped)
    (close-with-fvarso diff-deduped A A-generalized)))

(defne typing-state-o [gen gen-out ctx actx e B]
  
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



