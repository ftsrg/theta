(set-logic HORN)


(declare-fun |inv_main3| ( Int ) Bool)
(declare-fun |inv_main4| ( Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (= A 268435440)
      )
      (inv_main3 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv_main3 A)
        (and (<= 1 A) (<= 0 A) (= B (+ (- 2) A)))
      )
      (inv_main3 B)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (inv_main3 A)
        (and (<= 0 A) (not (<= 1 A)))
      )
      (inv_main4 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (inv_main4 A)
        (and (not (= B 0))
     (<= (- 1) B)
     (<= 0 A)
     (<= B 1)
     (or (not (<= 1 B)) (<= 1 A))
     (or (not (<= B (- 1))) (<= A (- 1)))
     (= A (+ (* 2 C) B)))
      )
      false
    )
  )
)

(check-sat)
(exit)
