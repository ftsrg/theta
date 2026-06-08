(set-logic HORN)


(declare-fun |inv| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (= A (- 1)) (= B 1))
      )
      (inv B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv D C)
        (and (= A (ite (<= 0 D) C (* 4 C))) (= B (* (- 2) D)))
      )
      (inv B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv B A)
        (and (not (<= B 5143523)) (= 0 (+ B A)))
      )
      false
    )
  )
)

(check-sat)
(exit)
