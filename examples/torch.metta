;Clean separation from Python calls
(= (tensor $x) (py-call (torch.tensor $x)))
(= (mul $A $B) (py-call (torch.matmul $A $B)))
(= (tensor2list $x) (py-call (.tolist $x)))
(= (size2list $x) (py-call (list $x)))
(= (shape $x) (size2list (py-call (getattr $x shape))))

;Clean program using Tensors:
(= (myprog)
   (let* (($A (tensor ((1 2 3)
                       (4 5 6))))
          ($B (tensor (( 7  8  9 10)
                       (11 12 13 14)
                       (15 16 17 18))))
          ($C (mul $A $B))
          ($S (shape $C))
          ($L (tensor2list $C)))
         ($L $S)))

!(test (myprog)
       (((74 80 86 92) (173 188 203 218)) (2 4)))
