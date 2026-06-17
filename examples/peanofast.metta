;Peano builders:
(= (expandK $expression $n)
   (if (== $n 0)
       done
       (let $temp1 (add-atom &self (num $expression))
            (expandK (S $expression) (- $n 1)))))

;Peano demo:
(= (demo-peano $K)
   (expandK Z $K))

!(demo-peano 2500)
!(test (length (collapse (match &self (num $1) $1))) 2500)
