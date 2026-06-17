(= (casetest $x)
   (case $x ((4 42)
             ($otherpattern 44)
             ($otherother $45))))
   
!(test (casetest 5) 44)
