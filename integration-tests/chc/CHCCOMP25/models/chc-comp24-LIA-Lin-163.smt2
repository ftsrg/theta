(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and (>= B 0) (>= A 0) (= A B) (= 0 v_2) (= 0 v_3))
      )
      (INV_MAIN_42 v_2 A v_3 B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 C A D B)
        (and (not (>= A 0)) (<= B 0) (not (= C (+ 1 D))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H)
        (and (= A (+ (- 1) H))
     (= D (+ 1 E))
     (= C (+ (- 1) F))
     (>= F 0)
     (not (<= H 0))
     (= B (+ 1 G)))
      )
      (INV_MAIN_42 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F)
        (and (= A (+ (- 1) D)) (>= D 0) (<= F 0) (= B (+ 1 C)))
      )
      (INV_MAIN_42 B A E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F)
        (and (= A (+ (- 1) F)) (not (>= D 0)) (not (<= F 0)) (= B (+ 1 E)))
      )
      (INV_MAIN_42 C D B A)
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
