;Clean separation from Python calls
(= (make-object) (py-call (types.SimpleNamespace)))
(= (get-attribute $obj $name) (py-call (getattr $obj $name)))
(= (set-attribute $obj $name $value) (py-call (setattr $obj $name $value)))
(= (import $name) (py-call (importlib.import_module $name)))
(= (math.pi) (get-attribute (import math) pi))

;Clean program using objects and pi: 
!(test (let* (($obj (make-object))
              ($temp (set-attribute $obj foo (math.pi))))
             (get-attribute $obj foo))
       3.141592653589793)
