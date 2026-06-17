!(add-atom &fdfd (cnt 37))

;This only works predictable single-threaded, else there is a data race:
(= (sloppyinc)
   (match &fdfd (cnt $x)
          ((remove-atom &fdfd (cnt $x))
           (let $inc (+ $x 1)
                     (add-atom &fdfd (cnt $inc))))))

;To protect from data reace we can use a mutex:
(= (mutexinc)
   (with_mutex testmutex
               (match &fdfd (cnt $x)
                      ((remove-atom &fdfd (cnt $x))
                       (let $inc (+ $x 1)
                            (add-atom &fdfd (cnt $inc)))))))

;Additionally we support transactions, the following illlustrates that remove-atom is undone if the nondet branch fails:
(= (Transaction_rollback_fail_to_inc)
   (transaction (match &fdfd (cnt $x)
                       ((remove-atom &fdfd (cnt $x))
                        (let $inc (+ $x 1)
                             (add-atom &fdfd (cnt $inc)))
                        (empty)))))

;even though swipl is threadsafe and will also not deadlock, this would cause aforementioned race condition between reading and writing:
;!(hyperpose ((sloppyinc) (sloppyinc) (sloppyinc) (sloppyinc) (sloppyinc)))

;while this is fine as all places modifying the (cnt $n) relation simultaneously (mutexinc only in this case) use the same mutex:
!(hyperpose ((mutexinc) (mutexinc) (mutexinc) (mutexinc) (mutexinc)))
!(test (collapse (get-atoms &fdfd)) ((cnt 42)))

;This won't affect the cnt since the transaction is setup to fail:
!(Transaction_rollback_fail_to_inc)
!(test (collapse (get-atoms &fdfd)) ((cnt 42)))
