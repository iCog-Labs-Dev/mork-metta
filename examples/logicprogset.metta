(= (myf $M)
   (and (and (member a $M)
             (member b $M))
        (== (size-atom $M) 2)))

!(test (if (once (myf $M)) $M)
       (a b))
