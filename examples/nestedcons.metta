(= (f (cons $a (cons $b $L)))
   $b)

!(test (f (a b c d)) b)
