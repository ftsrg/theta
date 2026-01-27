(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) (v_4 Int) ) 
    (=>
      (and
        (and (= A B) (= 0 v_2) (= 0 v_3) (= 0 v_4))
      )
      (INV_MAIN_42 v_2 v_3 A B v_4)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I)
        (and (= B (+ (- 1) H))
     (= C (+ 1 F))
     (= D (+ 1 E))
     (>= H 0)
     (<= E G)
     (= A (+ 1 I)))
      )
      (INV_MAIN_42 D C G B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G)
        (and (= B (+ 1 C)) (not (>= F 0)) (<= C E) (= A (+ 1 D)))
      )
      (INV_MAIN_42 B A E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G)
        (and (= B (+ (- 1) F)) (>= F 0) (not (<= C E)) (= A (+ 1 G)))
      )
      (INV_MAIN_42 C D E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E)
        (and (not (>= D 0)) (not (<= A C)) (not (= B E)))
      )
      false
    )
  )
)

(check-sat)
(exit)
