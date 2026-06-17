(= (facF $n)
   (if (== $n 0)
       1
       (* $n (facF (- $n 1)))))

!(test (facF 10) 3628800)
