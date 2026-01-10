(set-logic HORN)


(declare-fun |inv| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= C 1) (= B 0) (= A 1) (= D 0))
      )
      (inv D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv H G E F)
        (let ((a!1 (ite (= (mod (+ H G) 2) F) (+ 1 E) 0)))
  (and (= C (+ 2 G)) (= B a!1) (= A (+ 1 (* (- 1) F))) (= D (+ 1 H))))
      )
      (inv D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv A D B C)
        (and (= A 10) (= B A))
      )
      false
    )
  )
)

(check-sat)
(exit)
