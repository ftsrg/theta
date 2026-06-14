(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)
(declare-fun |f$unknown:1| ( Int ) Bool)
(declare-fun |h$unknown:6| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|f$unknown:1| A)
        (= B (+ 1 A))
      )
      (|f$unknown:2| B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|f$unknown:2| A B)
        (and (not (= 0 C)) (not (= (= 0 C) (>= B 0))))
      )
      (|h$unknown:6| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (not (= 0 B)) (not (= (= 0 B) (>= A 0))))
      )
      (|f$unknown:1| A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|h$unknown:6| B A)
        (and (= 0 C) (= (= 0 C) (<= B A)))
      )
      false
    )
  )
)

(check-sat)
(exit)
