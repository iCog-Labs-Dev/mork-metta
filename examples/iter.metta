; iterator state is just a number
(= (make-nat-iter) 0)

(= (iter-next $N)
   (let* (($X $N)
          ($Next (+ $N 1)))
         ($X $Next)))

!(test (let* (($it (make-nat-iter))
              (($x1 $it1) (iter-next $it))
              (($x2 $it2) (iter-next $it1))
              (($x3 $it3) (iter-next $it2)))
             ($x1 $x2 $x3))
       (0 1 2))
