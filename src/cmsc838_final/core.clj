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
  ([true])
  ([false]))

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

(defne not-forall-typeo [t]
  ([['v ?i]])
  ([[?t0 '-> ?t1]])
  (['bool]))

(defne -closed-typeo [t T]
  ([['v ?i] _] (nom/hash ?i T))
  ([[?t0 '-> ?t1] _] (-closed-typeo ?t0 T) (-closed-typeo ?t1 T))
  ([['∏ ?t] _]
   (fresh [?body]
     (nom/fresh [x]
       (== ?t (nom/tie x ?body))
       (-closed-typeo ?body T))))
  (['bool _]))

(defn closed-typeo [t]
  (-closed-typeo t t))

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


;; i think it's more efficient to construct a list
;; and check x \in list than checking x \in t
;; everytime
(defne type-fvo [t tvs]
  ([['v ?i] [?i]])
  ([['∏ ?t] _]
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
  ([_ [] true 'bool])
  ([_ [] false 'bool])
  
  ;; t-lam
  ([ctx [?A .  ?actx] _ [?A '-> ?B]]
   (nom/fresh [x]
     (fresh [?body]
       (== e ['λ (nom/tie x ?body)])
       (typingo (llist [x ?A] ctx) ?actx ?body ?B))))


  ;; t-lam2
  ([ctx [] _ [?t '-> ?B]]
   (nom/fresh [x]
     (fresh [?body]
       (== e ['λ (nom/tie x ?body)])
       (monotypeo ?t)
       (typingo (llist [x ?t] ctx) actx ?body ?B))))

  ;; t-lamann1
  ([ctx [?C . ?actx] _ [?C '-> ?B]]
   (nom/fresh [x]
     (fresh [?body ?A]
       (== e ['λ ?A (nom/tie x ?body)])
       (closed-typeo ?A)
       (subtypingo ?C ?A)
       (typingo (llist [x ?A] ctx) ?actx ?body ?B))))

  ;; t-lamann2
  ([ctx [] _ [?A '-> ?B]]
   (nom/fresh [x]
     (fresh [?body ?A]
       (== e ['λ ?A (nom/tie x ?body)])
       (closed-typeo ?A)
       (typingo (llist [x ?A] ctx) actx ?body ?B))))

  ;; t-gen is pulled out

  ;; t-app
  ([ctx actx ['ap ?e1 ?e2] ?C]
   (fresh [?A ?B]
     (typingo ctx [] ?e2 ?A)
     (t-geno ctx ?A ?B)
     (typingo ctx (llist ?B actx) ?e1 [?B '-> ?C])))

  ;; t-var
  ([_ _ ['v x] B]
   (fresh [A]
     (lookupo x A ctx)
     (application-subtypingo actx A B))))

(defne subtypingo [t0 t1]
  ;; s-forallr
  ([_ _]
   (not-forall-typeo t0)
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
  ([['v ?x] ['v ?x]])

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

(defn gen-typingo [ctx actx e t]
  (fresh [?t]
    (typingo ctx actx e ?t)
    (t-geno ctx ?t t)))

;; (run 1 [q] (typingo [['x 'bool]] [] ['fv 'x] q))

;; id infer
(run 1 [q] (nom/fresh [x]
             (gen-typingo [] [] ['λ (nom/tie x ['v x])] )))

;; fst infer
(run 2 [q] (nom/fresh [x y]
             (gen-typingo [] [] ['λ (nom/tie x ['λ (nom/tie y ['v x])])] q)))

;; ['ap id fst] check
(run 2 [q] (nom/fresh [x y]
             (fresh [?t]
               (typingo [] [] ['ap ['λ (nom/tie x ['v x])] ['λ (nom/tie x ['λ (nom/tie y ['v x])])]] q))))

;; snd infer
(run 1 [q] (nom/fresh [x y]
             (fresh [?t]
               (typingo [] [] ['λ (nom/tie x ['λ (nom/tie y ['v y])])] ?t)
               (t-geno [] ?t q))))

;; fst check
(run 1 [q] (nom/fresh [x y]
             (typingo [] []
                      ['ap ['λ (nom/tie x ['v x])] ['λ (nom/tie x ['λ (nom/tie y ['v x])])]]
                      ['∏ (nom/tie x ['∏ (nom/tie y [['v x] '-> [['v y] '-> ['v x]]])])])))


(run 20 [q] (fresh [t]
             (gen-typingo [] [] q t)))

(defne substo [x e body out]
  ([_ _ ['v x] e])
  ([_ _ _ body]
   (nom/hash x body))
  ([_ _ _ _]
   (nom/fresh [y]
     (fresh [?body ?out]
       (== ['λ (nom/tie y ?body)] body)
       (substo x e ?body ?out)
       (== out ['λ (nom/tie y ?out)]))))
  ([_ _ _ _]
   (nom/fresh [y]
     (fresh [?body ?out ?A]
       (== ['λ ?A (nom/tie y ?body)] body)
       (substo x e ?body ?out)
       (== out ['λ ?A (nom/tie y ?out)]))))
  ([_ _ ['ap ?e0 ?e1] ['ap ?e0-out ?e1-out]]
   (substo x e ?e0 ?e0-out)
   (substo x e ?e1 ?e1-out)))


(defne call-by-nameo [e e-nf]
  ([true true])
  ([false false])

  ([['v x] e])

  ([['ap ?e0 ?e1] _]
   (nom/fresh [x]
     (fresh [?body ?e-subst]
       (conde
        ((call-by-nameo ?e0 ['λ (nom/tie x ?body)])
         (substo x ?e1 ?body ?e-subst)
         (call-by-nameo ?e-subst e-nf))
        ((fresh [y ?e1-out]
           (call-by-nameo ?e0 ['v y])
           (call-by-nameo ?e1 ?e1-out)
           (== e-nf ['ap ['v y] ?e1-out])))))))

  ([_ _]
   (nom/fresh [x]
     (fresh [?body ?body-out]
       (== e ['λ (nom/tie x ?body)])
       (call-by-nameo ?body ?body-out)
       (== e-nf ['λ (nom/tie x ?body-out)]))))
  ([_ _]
   (nom/fresh [x]
     (fresh [?A ?body ?body-out]
       (== e ['λ ?A (nom/tie x ?body)])
       (call-by-nameo ?body ?body-out)
       (== e-nf ['λ ?A (nom/tie x ?body-out)])))))

(run 1 [e T]
  (gen-typingo [] [] e T)
  (call-by-nameo ['ap ['ap e false] true] true))

(run 1 [e T]
  (call-by-nameo ['ap ['ap e false] true] true)
  (gen-typingo [] [] e T))

;; (run 1 [e T]
;;   (call-by-nameo ['ap e true] true)
;;   (call-by-nameo ['ap e false] true)
;;   (gen-typingo [] [] e T))

(run 1 [e T]
  (fresh [const-true const-false t0 t1]
    (call-by-nameo ['ap const-true true] true)
    (call-by-nameo ['ap const-true false] true)
    (call-by-nameo ['ap const-false true] false)
    (call-by-nameo ['ap const-false false] false)
    (gen-typingo [] [] const-true t0)
    (gen-typingo [] [] const-false t1)
    (gen-typingo [] [] e T)
    (call-by-nameo ['ap ['ap e false] true] true)))

(run 1 [e T]
  (nom/fresh [x]
    (gen-typingo [] [] ['λ (nom/tie x true)]  T)))

