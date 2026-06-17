!(import! &self ../lib/lib_spaces)

;fail test:
!(test (succeedsPredicate (&self friend tim tom))
       False)

;metta s-expr:
(friend a b)
!(test (if (succeedsPredicate (&self friend $a $b))
           ($a $b)
           NotFound)
       (a b))
