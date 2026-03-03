(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= A C) (= B D) (= 0 v_4) (= 0 v_5) (= 0 v_6) (= 0 v_7))
      )
      (INV_MAIN_42 B v_4 A v_5 v_6 D C v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (INV_MAIN_42 F G H I J K L M)
        (and (= B (ite (= J 10) 10 (+ 5 K)))
     (= C (+ 1 J))
     (= D (+ I (* 5 G) F))
     (= E (+ 1 G))
     (not (<= H G))
     (not (<= L J))
     (= A (+ M K)))
      )
      (INV_MAIN_42 F E H D C B L A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (and (= B (+ 1 D)) (not (<= E D)) (<= I G) (= A (+ F (* 5 D) C)))
      )
      (INV_MAIN_42 C B E A G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I J K)
        (and (= B (ite (= H 10) 10 (+ 5 I)))
     (= C (+ 1 H))
     (<= F E)
     (not (<= J H))
     (= A (+ K I)))
      )
      (INV_MAIN_42 D E F G C B J A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (and (<= C B) (<= G E) (not (= D H)))
      )
      false
    )
  )
)

(check-sat)
(exit)
