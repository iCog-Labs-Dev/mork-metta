(= (clamp $v $min $max)
   (min $max (max $v $min)))

(: smallest-intersection-probability (-> Number Number Number))
(= (smallest-intersection-probability $As $Bs)
   (clamp (/ (- (+ $As $Bs) 1) $As) 0 1))

(: largest-intersection-probability (-> Number Number Number))
(= (largest-intersection-probability $As $Bs)
   (clamp (/ $Bs $As) 0 1))

(: conditional-probability-consistency (-> Number Number Number Bool))
(= (conditional-probability-consistency $As $Bs $ABs)
   (and (< 0 $As)
        (and (<= (smallest-intersection-probability $As $Bs) $ABs)
             (<= $ABs (largest-intersection-probability $As $Bs)))))

(= (Truth_Deduction (stv $Ps $Pc)
                    (stv $Qs $Qc)
                    (stv $Rs $Rc)
                    (stv $PQs $PQc)
                    (stv $QRs $QRc))
   (if (and (conditional-probability-consistency $Ps $Qs $PQs)
            (conditional-probability-consistency $Qs $Rs $QRs))
       ;; Preconditions are met
       (stv (if (< 0.9999 $Qs)                  ; avoid division by 0
                ;; Qs tends to 1
                $Rs
                ;; Otherwise
                (+ (* $PQs $QRs) (/ (* (- 1 $PQs) (- $Rs (* $Qs $QRs))) (- 1 $Qs))))
            (min $Pc (min $Qc (min $Rc (min $PQc $QRc)))))
       ;; Preconditions are not met
       (stv 1 0)))

(= (STV a) (stv 0.4 0.9))
(= (STV b) (stv 0.4 0.9))
(= (STV c) (stv 0.4 0.9))

(= (sentence (Inheritance a b) (stv 0.9 0.9)) (once True))
(= (sentence (Inheritance b c) (stv 0.9 0.9)) (once True))
(= (sentence (Inheritance $A $C) $TV)
   (once (and (and (sentence (Inheritance $A $B) $T1)
                   (sentence (Inheritance $B $C) $T2))
              (= $TV (Truth_Deduction (STV $A) (STV $B) (STV $C) $T1 $T2)))))

!(test (let $derivation (sentence (Inheritance a c) $TV) $TV)
       (stv 0.8166666666666668 0.9))
