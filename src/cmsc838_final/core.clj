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
     (== ['S ?o] o)
     (pluso ?x y ?o) )))

(defn leqo [x y]
  (fresh (z)
    (pluso z x y)))

(defn leo [x y]
  (fresh (z)
    (leqo ['S x] y)))

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
(defn termo [e]
  (term-i-o 'Z e))
;; keeps track of the # of lambdas
(defne term-i-o [m-i e]
  ([_ _] (boolo e))
  ([_ ['bv i]] (leo i m-i)) ;; not necessary to check i is nat in this case
  ([_ ['fv i]] (nato i))
  ([_ ['λ ?e]] (term-i-o ['S m-i] ?e))
  ([_ [e0 e1]] (term-i-o m-i e0) (term-i-o m-i e1)))

(defn typeo [t]
  (type-i-o 'Z t))

(defne type-i-o [m-i t]
  ([_ 'bool])
  ([_ ['Λ ?t]] (type-i-o ['S m-i] ?t))
  ([_ [?t0 '-> ?t1]] (type-i-o m-i ?t0) (type-i-o m-i ?t1))
  ([_ ['bv ?i]] (leo ?i m-i))
  ([_ ['fv ?i]] (nato ?i)))

(def type-fst
  '(Λ (Λ ((bv (S Z)) -> ((bv Z) -> (bv (S Z)))))))

;; (run* [q] (typeo type-fst))


(def type-snd
  '(Λ (Λ ((bv (S Z)) -> ((bv Z) -> (bv Z))))))

;; (run* [q] (typeo type-snd))


(defn monotypeo [t]
  (monotype-i-o 'Z t))

(defne monotype-i-o [m-i t]
  ([_ 'bool])
  ([_ [?t0 '-> ?t1]] (monotype-i-o m-i ?t0) (monotype-i-o m-i ?t1))
  ([_ ['bv ?i]] (leo ?i m-i))
  ([_ ['fv ?i]] (nato ?i)))

