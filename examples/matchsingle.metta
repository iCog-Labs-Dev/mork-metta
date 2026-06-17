(a b)
(a c)

(= (match-single-via-cut $space $pattern $outPattern)
   (let* (($x (match $space $pattern $outPattern))
          ($temp (cut)))
         $x))

(= (match-single-via-once $space $pattern $outPattern)
   (once (match $space $pattern $outPattern)))

!(test (collapse (match-single-via-cut &self (a $x) (a $x))) ((a b)))
!(test (collapse (match-single-via-once &self (a $x) (a $x))) ((a b)))
