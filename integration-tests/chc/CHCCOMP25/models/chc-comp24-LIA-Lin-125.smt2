(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)
(declare-fun |f$unknown:1| ( Int ) Bool)
(declare-fun |g$unknown:5| ( Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (|f$unknown:1| A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|f$unknown:2| A B)
        true
      )
      (|g$unknown:5| A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|f$unknown:1| A)
        (and (= 0 B) (= C 0) (not (= (= 0 B) (>= A 0))))
      )
      (|f$unknown:2| C A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|g$unknown:5| A)
        (and (= 0 B) (not (= (= 0 B) (= A 0))))
      )
      false
    )
  )
)

(check-sat)
(exit)
