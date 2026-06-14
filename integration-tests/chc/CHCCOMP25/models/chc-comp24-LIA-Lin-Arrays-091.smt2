(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (and (= C G) (= B F) (= A E) (= D H) (= 0 v_8) (= v_9 F))
      )
      (INV_MAIN_42 A v_8 C B D E G F v_9 H)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N Int) (O (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F G H I J K L M N O)
        (let ((a!1 (store J (+ F (* 4 G)) (select J (+ I (* 4 G)))))
      (a!2 (<= L (div (+ N (* (- 1) M)) 4))))
  (and (= D a!1)
       (= B (+ 4 N))
       (= C (+ 4 K))
       (= E (+ 1 G))
       (not a!2)
       (not (<= H G))
       (= A (store O K (select O N)))))
      )
      (INV_MAIN_42 F E H I D C L M B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J K L)
        (let ((a!1 (<= I (div (+ K (* (- 1) J)) 4)))
      (a!2 (store G (+ C (* 4 D)) (select G (+ F (* 4 D))))))
  (and (= B (+ 1 D)) a!1 (not (<= E D)) (= A a!2)))
      )
      (INV_MAIN_42 C B E F A H I J K L)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I J K L M)
        (let ((a!1 (<= J (div (+ L (* (- 1) K)) 4))))
  (and (= B (+ 4 L))
       (= C (+ 4 I))
       (not a!1)
       (<= F E)
       (= A (store M I (select M L)))))
      )
      (INV_MAIN_42 D E F G H C J K B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= G (div (+ I (* (- 1) H)) 4))))
  (and a!1 (<= C B) (not (= E J))))
      )
      false
    )
  )
)

(check-sat)
(exit)
