(: Z Nat)
(: S (-> Nat Nat))
(: Greater (-> Nat Nat Bool))
(= (Greater (S $x) Z)
   True)
(= (Greater Z $x)
   False)
(= (Greater (S $x) (S $y))
   (Greater $x $y))

!(test (Greater (S Z) (S Z)) false)    ; False
!(test (Greater (S (S Z)) (S Z)) true) ; True
