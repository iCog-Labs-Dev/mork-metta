(foo 1)
(foo 2)
(foo 42 42)
(foo (42 42))

!(bar 42)
!(bar 43)

(= (answer) 42)

!(test (space (msort (collapse (superpose ((match &self (foo $1) (foo $1))
                                           (match &self (foo $1 $2) (foo $1 $2))
                                           (match &self (bar $1) (bar $1)))))) (answer))
       (space ((foo (42 42)) (foo 1) (foo 2) (foo 42 42)) 42))
