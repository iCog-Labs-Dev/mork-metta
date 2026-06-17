(: apply (-> (-> $tx $ty) $tx $ty))
(= (apply $f $x) ($f $x))
!(apply not False) ; True
!(get-type (apply not False))
!(test (let (get-type apply) (-> (-> Bool Bool) Bool $result) $result)
       Bool)
