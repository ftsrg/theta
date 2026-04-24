(set-logic HORN)


(declare-fun |inv| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= A 0) (not (<= C B)) (= D 0))
      )
      (inv D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv F C B E)
        (and (= D (+ 1 F)) (= A (ite (<= B F) (+ (- 2) E) (+ 1 E))))
      )
      (inv D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv D C B A)
        (and (<= A 0) (not (<= D (+ C B))))
      )
      false
    )
  )
)

(check-sat)
(exit)
