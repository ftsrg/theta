(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (= A B) (= 0 v_2) (= 0 v_3) (= 1 v_4) (= 0 v_5))
      )
      (INV_MAIN_1 v_2 A v_3 v_4 B v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_1 A B E C D F)
        (and (not (<= A B)) (not (<= C D)) (not (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_1 G E F J H I)
        (and (= A (+ I J)) (= D (+ 1 G)) (= C (+ F G)) (<= G E) (<= J H) (= B (+ 1 J)))
      )
      (INV_MAIN_1 D E C B H A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 E C D F G H)
        (and (= A (+ D E)) (<= E C) (not (<= F G)) (= B (+ 1 E)))
      )
      (INV_MAIN_1 B C A F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 C D E H F G)
        (and (= A (+ G H)) (not (<= C D)) (<= H F) (= B (+ 1 H)))
      )
      (INV_MAIN_1 C D E B F A)
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
