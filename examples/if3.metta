!(test (if (is-var $A) 
           (if True 42 lol) 
           (+ 2 2)) 42)
