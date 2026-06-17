!(test (if (if (== 42 42) True False)
           (if True 42 lol) 
           (+ 2 2)) 42)
