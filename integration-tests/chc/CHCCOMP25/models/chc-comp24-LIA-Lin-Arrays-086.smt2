(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F) (= 0 v_6) (= 0 v_7))
      )
      (INV_MAIN_42 A v_6 B C D v_7 E F)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J K L)
        (let ((a!1 (store H (+ 4 E (* 4 F)) (select H (+ E (* 4 F)))))
      (a!2 (= A (store L (+ 4 I (* 4 J)) (select L I)))))
  (and (= C a!1) (= B (+ 1 J)) (= D (+ 1 F)) (not (<= K J)) (not (<= G F)) a!2))
      )
      (INV_MAIN_42 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (store F (+ 4 C (* 4 D)) (select F (+ C (* 4 D))))))
  (and (= B (+ 1 D)) (<= I H) (not (<= E D)) (= A a!1)))
      )
      (INV_MAIN_42 C B E A G H I J)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (= A (store J (+ 4 G (* 4 H)) (select J G)))))
  (and (= B (+ 1 H)) (not (<= I H)) (<= E D) a!1))
      )
      (INV_MAIN_42 C D E F G B I A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (and (<= C B) (or (not (= B F)) (not (= D H))) (<= G F))
      )
      false
    )
  )
)

(check-sat)
(exit)
