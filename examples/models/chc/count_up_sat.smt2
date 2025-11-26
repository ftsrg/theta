(set-logic HORN)

(declare-fun |inv| ( Int ) Bool)

(assert
  (forall ( (v_0 Int) ) 
    (=>
      (and
        (= 0 v_0)
      )
      (inv v_0)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv A)
        (< A 5)
        (and (= B (+ 1 A)))
      )
      (inv B)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (inv A)
        (= A 6)
      )
      false
    )
  )
)

(check-sat)
(exit)