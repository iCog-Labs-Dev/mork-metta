(= (f $x)
   (* $x 2))

(= (g $f $x)
   (justdata $f $x))

(= (h $f $x)
   ($f $x))

(= (notjustdata $x)
   f)

(= (datawithnondatacomponent)
   ((lol (f 42))))

!(test ((f 21) (g f 2) (h f 2) ((notjustdata 42) 21) (datawithnondatacomponent))
       (42 (justdata f 2) 4 42 ((lol 84))))
