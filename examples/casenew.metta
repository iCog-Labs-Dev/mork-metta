(= (wu1)
   (empty))

(= (wu2)
   (full))

(= (wu)
   (superpose ((wu1)
               (wu2))))

!(test (wu)
       (full))
