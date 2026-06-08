(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int ) Bool)
(declare-fun |END_QUERY| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (= A B) (= 1 v_2) (= 0 v_3) (= 0 v_4) (= 0 v_5))
      )
      (INV_MAIN_42 v_2 v_3 A v_4 v_5 B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 A E B C F D)
        (and (not (<= A B)) (<= D C) (not (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J)
        (and (= A (+ 2 I))
     (= D (+ 1 E))
     (= C (+ 2 F))
     (<= E G)
     (not (<= J H))
     (= B (+ 1 H)))
      )
      (INV_MAIN_42 D C G B A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (and (= A (+ 2 D)) (<= C E) (<= H F) (= B (+ 1 C)))
      )
      (INV_MAIN_42 B A E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (and (= A (+ 2 G)) (not (<= C E)) (not (<= H F)) (= B (+ 1 F)))
      )
      (INV_MAIN_42 C D E B A H)
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
