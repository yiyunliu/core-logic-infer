(ns cmsc838-final.core
  (:refer-clojure :exclude [==])
  (:use clojure.core.logic)
  (:require [clojure.core.logic.fd :as fd])
  (:require [clojure.core.match :refer [match]])
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


;; syntax for our terms
;; keeps track of the # of lambdas
(defne term-i-o [m-i e]
  ([_ _] (boolo e))
  ([_ ['bv i]] (lto i m-i)) ;; not necessary to check i is nat in this case
  ([_ ['fv i]])
  ([_ ['λ ?e]] (term-i-o (list 'S m-i) ?e))
  ([_ ['ap e0 e1]] (term-i-o m-i e0) (term-i-o m-i e1)))

(defn termo [e]
  (term-i-o 'Z e))


(defne type-i-o [m-i t]
  ([_ 'bool])
  ([_ ['Λ ?t]] (type-i-o (list 'S m-i) ?t))
  ([_ [?t0 '-> ?t1]] (type-i-o m-i ?t0) (type-i-o m-i ?t1))
  ([_ ['bv ?i]] (lto ?i m-i))
  ([_ ['fv ?i]]))


(defn typeo [t]
  (type-i-o 'Z t))


(def type-fst
  '(Λ (Λ ((bv (S Z)) -> ((bv Z) -> (bv (S Z)))))))

;; (run* [q] (typeo type-fst))


(def type-snd
  '(Λ (Λ ((bv (S Z)) -> ((bv Z) -> (bv Z))))))

;; (run* [q] (typeo type-snd))


(defne monotypeo [t]
  (['bool])
  ([[?t0 '-> ?t1]] (monotypeo ?t0) (monotypeo ?t1))
  ([['fv ?i]]))




;; precondition: t is a term
(defne term-nocheck-openo [k x t t-opened]
  ;; open
  ([_ _ _ _] (boolo t) (== t-opened t))
  ([_ _ ['bv k] ['fv x]])
  ([_ _ ['bv ?k] _] (!= ?k k))
  ([_ _ ['fv ?x] ['fv ?x]])
  ([_ _ ['λ ?e] _] (fresh (?e-opened)
                     (== ['λ ?e-opened] t-opened)
                     (term-nocheck-openo (list 'S k) x ?e ?e-opened)))
  ;; bug bug bug!!
  ([_ _ ['ap ?e0 ?e1] _] (fresh (?e0-opened ?e1-opened)
                       (== t-opened (list 'ap ?e0-opened ?e1-opened))
                       (term-nocheck-openo k x ?e0 ?e0-opened)
                           (term-nocheck-openo k x ?e1 ?e1-opened))))

(defne term-nocheck-closeo [k x t t-closed]
  ;; open
  ([_ _ _ _] (boolo t) (== t-closed t))
  ([_ _ ['bv _] t])
  ([_ _ ['fv x] ['bv k]])
  ([_ _ ['fv ?x] ['bv k]] (!= ?x x))
  ([_ _ ['λ ?e] _] (fresh (?e-closed)
                     (== ['λ ?e-closed] t-closed)
                     (term-nocheck-closeo (list 'S k) x ?e ?e-closed)))
  ;; bug bug bug!!
  ([_ _ ['ap ?e0 ?e1] _] (fresh (?e0-closed ?e1-closed)
                       (== t-closed (list 'ap ?e0-closed ?e1-closed))
                       (term-nocheck-closeo k x ?e0 ?e0-closed)
                       (term-nocheck-closeo k x ?e1 ?e1-closed))))


(defn term-openo [x t t-opened]
  (term-nocheck-openo 'Z x t t-opened))


;; can't be defined in terms of openo
(defn term-closeo [x t t-closed]
  (term-nocheck-closeo 'Z x t t-closed))

;; (run* [q] (term-closeo 'x  '(λ (fv x)) q))


(defne type-nocheck-openo [k x t t-opened]
  ;; open
  ([_ _ 'bool 'bool])
  ([_ _ ['bv k] ['fv x]])
  ([_ _ ['bv ?k] _] (!= ?k k))
  ([_ _ ['fv ?x] ['fv ?x]])
  ([_ _ ['Λ ?e] _] (fresh (?e-opened)
                     (== ['Λ ?e-opened] t-opened)
                     (type-nocheck-openo (list 'S k) x ?e ?e-opened)))
  ;; bug bug bug!!
  ([_ _ [?e0 '-> ?e1] _] (fresh (?e0-opened ?e1-opened)
                       (== t-opened (list ?e0-opened '-> ?e1-opened))
                       (type-nocheck-openo k x ?e0 ?e0-opened)
                           (type-nocheck-openo k x ?e1 ?e1-opened))))

(defne type-nocheck-closeo [k x t t-closed]
  ;; open
  ([_ _ _ _] (boolo t) (== t-closed t))
  ([_ _ ['bv ?k] t])
  ([_ _ ['fv x] ['bv k]])
  ([_ _ ['fv ?x] ['bv k]] (!= ?x x))
  ([_ _ ['Λ ?e] _] (fresh (?e-closed)
                     (== ['Λ ?e-closed] t-closed)
                     (type-nocheck-closeo (list 'S k) x ?e ?e-closed)))
  ;; bug bug bug!!
  ([_ _ [?e0 '-> ?e1] _] (fresh (?e0-closed ?e1-closed)
                       (== t-closed (list ?e0-closed '-> ?e1-closed))
                       (type-nocheck-closeo k x ?e0 ?e0-closed)
                       (type-nocheck-closeo k x ?e1 ?e1-closed))))


(defn type-openo [x t t-opened]
  (type-nocheck-openo 'Z x t t-opened))


;; can't be defined in types of openo
(defn type-closeo [x t t-closed]
  (type-nocheck-closeo 'Z x t t-closed))
