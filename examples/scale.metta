; --- bulk insert K atoms: (r K (mod K 10)), (r K-1 ...), ..., (r 1 ...)
(= (addK $K)
   (if (== $K 0)
       done
       (let* (($K10 (% $K 10))
              ($t (add-atom &self (r $K $K10))))
              (addK (- $K 1)))))

; --- query patterns to exercise different indexes
(= (q-all)
   (collapse (match &self (r $x $y) (r $x $y))))

(= (q-first $a)
   (collapse (match &self (r $a $y) (r $a $y))))

(= (q-second $b)
   (collapse (match &self (r $x $b) (r $x $b))))

(= (q-both $a $b)
   (collapse (match &self (r $a $b) (r $a $b))))

(= (q-rel $r)
   (collapse (match &self ($r 643 3) ($r 643 3))))

; --- driver: load K, then return results of 4 query shapes
(= (indexing-demo $K)
   (let* (($temp (addK $K))
          ($all (q-all))
          ($first (q-first 7))
          ($second (q-second 3))
          ($rel (q-rel r))
          ($both (q-both 42 2)))
         (all: (length $all) first: (length $first) second: (length $second) rel: (length $rel) both: (length $both))))

;Just the elements
!(test (indexing-demo 1000000)
       (all: 1000000 first: 1 second: 100000 rel: 1 both: 1))
