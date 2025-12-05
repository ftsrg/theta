(set-logic HORN)


(declare-fun |INV_MAIN_2| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (= A B) (= 1 v_2) (= 1 v_3) (= 1 v_4) (= 1 v_5))
      )
      (INV_MAIN_1 v_2 A v_3 v_4 B v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J)
        (and (= B (+ 1 H)) (= C (* 5 G)) (= D (+ 1 E)) (<= H I) (<= E F) (= A (* 5 J)))
      )
      (INV_MAIN_1 D F C B I A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H)
        (and (= B (+ 1 C)) (not (<= F G)) (<= C D) (= A (* 5 E)))
      )
      (INV_MAIN_1 B D A F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H)
        (and (= B (+ 1 F)) (<= F G) (not (<= C D)) (= A (* 5 H)))
      )
      (INV_MAIN_1 C D E B G A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F)
        (and (not (<= A B)) (not (<= D E)) (= 0 v_6) (= 1 v_7))
      )
      (INV_MAIN_2 v_6 B C v_7 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_2 E F G H I J)
        (and (= B (+ 1 H)) (= C (+ G E)) (= D (+ 1 E)) (<= H I) (<= E F) (= A (+ J H)))
      )
      (INV_MAIN_2 D F C B I A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H)
        (and (= B (+ 1 C)) (not (<= F G)) (<= C D) (= A (+ E C)))
      )
      (INV_MAIN_2 B D A F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H)
        (and (= B (+ 1 F)) (<= F G) (not (<= C D)) (= A (+ H F)))
      )
      (INV_MAIN_2 C D E B G A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F)
        (and (not (<= D E)) (not (<= A B)) (not (= C F)))
      )
      false
    )
  )
)

(check-sat)
(exit)
