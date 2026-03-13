(set-logic HORN)


(declare-fun |f$unknown:4| ( Int Int ) Bool)
(declare-fun |decr$unknown:2| ( Int Int ) Bool)
(declare-fun |f$unknown:6| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (= A (+ (- 1) B))
      )
      (|decr$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|decr$unknown:2| A C)
        (= B 3)
      )
      (|f$unknown:4| A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|f$unknown:4| D B)
        (and (not (= 0 C)) (= A D) (= (= 0 C) (<= B 0)))
      )
      (|f$unknown:6| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (= 0 C) (= A 1) (= (= 0 C) (<= B 0)))
      )
      (|f$unknown:6| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|f$unknown:6| B A)
        (and (= 0 C) (= A 3) (= (= 0 C) (<= B 0)))
      )
      false
    )
  )
)

(check-sat)
(exit)
