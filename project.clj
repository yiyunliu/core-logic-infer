(defproject cmsc838-final "0.1.0-SNAPSHOT"
  :description "A HM-style typechecker implemented using core.logic"
  :url "https://github.com/yiyunliu/cmsc838-final"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [org.clojure/core.match "1.0.0"]
                 [org.clojure/core.logic "1.0.0"]]
  :main ^:skip-aot cmsc838-final.core
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all}})
