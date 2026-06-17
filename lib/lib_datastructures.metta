;;; EFFICIENT AMORTIZED O(1) OP FUNCTIONAL QUEUE ;;;

;Enqueue adds 1 to N
(= (enqueue $E (queue $In $Out $N))
   (queue (cons $E $In) $Out (+ $N 1)))

;Normal dequeue subtracts 1
(= (dequeue $E (queue $In (cons $E $Out) $N))
   (queue $In $Out (- $N 1)))

;When out empty, reverse in and subtract 1
(= (dequeue $E (queue $In () $N))
   (let (cons $E $R) (reverse $In)
        (queue () $R (- $N 1))))

;Empty queue
(= (empty-queue) (queue () () 0))

;;; EFFICIENT O(1) LOOKUP SPACE ;;;

;Fast Hashmap-like existence check via repra:
(= (add-unique-or-fail $space $Expression)
   (let $st (s (repra $Expression))
        (if (== () (collapse (once (match $space $st True))))
            (add-atom $space $st)
            (empty))))
