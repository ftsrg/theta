(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (v_1 Int) ) 
    (=>
      (and
        (and true (= v_1 A))
      )
      (|f$unknown:2| A v_1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (|f$unknown:2| B A)
        (let ((a!1 (= (= 0 E) (and (not (= 0 C)) (not (= 0 D))))))
  (and (not (= (= 0 D) (<= B 0)))
       (= (= 0 C) (<= A 0))
       (not (= (= 0 F) (= 0 E)))
       (= 0 F)
       (not a!1)))
      )
      false
    )
  )
)

(check-sat)
(exit)
