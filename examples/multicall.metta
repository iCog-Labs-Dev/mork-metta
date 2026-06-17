(= (mycalc $x $y)
   (+ $x $y))

(= (mycalc $x $y)
   (- $x $y))

!(test (collapse (mycalc 1 2))
       (3 -1))
