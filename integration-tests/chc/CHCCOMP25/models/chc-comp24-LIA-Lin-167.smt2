(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and (= A B) (= 1 v_2) (= 1 v_3))
      )
      (INV_MAIN_42 v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B)
        (and (>= B 3) (not (<= A 2)) (not (= (* 4 A) (* 4 B))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D)
        (and (= B (+ 4 (* 2 C))) (not (>= D 3)) (<= C 2) (= A (+ 4 (* 2 D))))
      )
      (INV_MAIN_42 B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (INV_MAIN_42 B C)
        (and (>= C 3) (<= B 2) (= A (+ 4 (* 2 B))))
      )
      (INV_MAIN_42 A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (INV_MAIN_42 B C)
        (and (not (>= C 3)) (not (<= B 2)) (= A (+ 4 (* 2 C))))
      )
      (INV_MAIN_42 B A)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        END_QUERY
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
