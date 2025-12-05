(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (= A (+ 1 B)) (= 0 v_2) (= 1 v_3) (= 1 v_4) (= 1 v_5))
      )
      (INV_MAIN_42 v_2 v_3 A v_4 v_5 B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_42 G H I J K L)
        (and (= B (+ J K))
     (= C (+ J K))
     (= D (+ (- 1) I))
     (= E (+ G H))
     (= F (+ G H))
     (not (<= I 0))
     (not (<= L 0))
     (= A (+ (- 1) L)))
      )
      (INV_MAIN_42 F E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I)
        (and (= B (+ D E)) (= C (+ D E)) (not (<= F 0)) (<= I 0) (= A (+ (- 1) F)))
      )
      (INV_MAIN_42 C B A G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I)
        (and (= B (+ G H)) (= C (+ G H)) (<= F 0) (not (<= I 0)) (= A (+ (- 1) I)))
      )
      (INV_MAIN_42 D E F C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (<= C 0) (<= F 0) (not (= B E)))
      )
      false
    )
  )
)

(check-sat)
(exit)
