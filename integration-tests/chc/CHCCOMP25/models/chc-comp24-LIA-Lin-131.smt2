(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)
(declare-fun |f$unknown:1| ( Int ) Bool)
(declare-fun |h$unknown:5| ( Int ) Bool)

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
        (and (not (= 0 C)) (= (= 0 C) (<= B 0)))
      )
      (|h$unknown:5| A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (not (= 0 B)) (= (= 0 B) (<= A 0)))
      )
      (|f$unknown:1| A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|h$unknown:5| A)
        (and (= 0 B) (= (= 0 B) (<= A 0)))
      )
      false
    )
  )
)

(check-sat)
(exit)
