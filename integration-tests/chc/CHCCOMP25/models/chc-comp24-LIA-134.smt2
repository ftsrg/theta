(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)
(declare-fun |twice$unknown:4| ( Int Int ) Bool)
(declare-fun |twice$unknown:6| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (= A (* 2 B))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|f$unknown:2| A D)
        (and (not (= 0 C)) (= (= 0 C) (<= B 0)))
      )
      (|twice$unknown:4| A D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|twice$unknown:4| C B)
        (|twice$unknown:4| D C)
        (= A D)
      )
      (|twice$unknown:6| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|twice$unknown:6| C A)
        (and (= (= 0 D) (<= C A)) (not (= 0 B)) (= 0 D) (= (= 0 B) (<= A 0)))
      )
      false
    )
  )
)

(check-sat)
(exit)
