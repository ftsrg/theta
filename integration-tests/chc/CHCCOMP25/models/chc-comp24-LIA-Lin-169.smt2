(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int ) Bool)
(declare-fun |END_QUERY| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= B (ite (<= 1 C) C 1))
     (= C D)
     (= A (ite (<= 1 D) D 1))
     (= 1 v_4)
     (= 0 v_5)
     (= 1 v_6)
     (= 2 v_7))
      )
      (INV_MAIN_42 B v_4 v_5 A v_6 v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 B A E D C F)
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
        (and (= B (+ 1 I))
     (= A (+ 2 J))
     (= D (+ 1 F))
     (<= F E)
     (not (<= H I))
     (= C (+ 2 G)))
      )
      (INV_MAIN_42 E D C H B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (and (= B (+ 1 D)) (<= D C) (<= F G) (= A (+ 2 E)))
      )
      (INV_MAIN_42 C B A F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (and (= B (+ 1 G)) (not (<= D C)) (not (<= F G)) (= A (+ 2 H)))
      )
      (INV_MAIN_42 C D E F B A)
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
