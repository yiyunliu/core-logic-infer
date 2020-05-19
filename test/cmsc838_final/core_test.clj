(ns cmsc838-final.core-test
  (:require [clojure.test :refer :all]
            [cmsc838-final.core :refer :all]))


(deftest test-typingo
  (testing "t-var"
    (is (= '(bool) (infer-with-ctx-1 [['x 'bool]] [] ['fv 'x])))
    (is (= '(bool) (infer-with-ctx-1 [] [] '[λ [bv Z]])))))
