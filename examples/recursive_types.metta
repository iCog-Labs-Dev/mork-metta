(: blacksmith (-> Metal Sword))
(: blacksmith (-> Metal Paperclip))
(: iron Metal)
(: gold Metal)

!(test (get-type iron) Metal)
!(test (collapse (get-type blacksmith)) ((-> Metal Sword) (-> Metal Paperclip)))
!(test (collapse (get-type (blacksmith iron))) (Sword Paperclip))
!(test (collapse (get-type (iron blacksmith))) ((Metal (-> Metal Sword)) (Metal (-> Metal Paperclip))))
