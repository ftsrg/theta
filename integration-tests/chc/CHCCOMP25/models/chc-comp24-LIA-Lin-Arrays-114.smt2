(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (and (= C G) (= B F) (= A E) (= D H) (= 0 v_8) (= v_9 G))
      )
      (INV_MAIN_42 A v_8 B C D E F G v_9 H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B I C H G F J)
        (let ((a!1 (<= H (div (+ F (* (- 1) G)) 4))))
  (and a!1 (<= E D) (not (= I J))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) ) 
    (=>
      (and
        (INV_MAIN_42 G J F I H M K L O N)
        (let ((a!1 (<= K (div (+ O (* (- 1) L)) 4)))
      (a!2 (store H (+ G (* 4 J)) (select H (+ I (* 4 J))))))
  (and (= A (store N M (select N O)))
       (= E (+ 1 J))
       (= C (+ 4 M))
       (= B (+ 4 O))
       (not (<= F J))
       (not a!1)
       (= D a!2)))
      )
      (INV_MAIN_42 G E F I D C K L B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D G C F E H I J K L)
        (let ((a!1 (<= I (div (+ K (* (- 1) J)) 4)))
      (a!2 (store E (+ D (* 4 G)) (select E (+ F (* 4 G))))))
  (and (= B (+ 1 G)) (not (<= C G)) a!1 (= A a!2)))
      )
      (INV_MAIN_42 D B C F A H I J K L)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H K I J M L)
        (let ((a!1 (<= I (div (+ M (* (- 1) J)) 4))))
  (and (= C (+ 4 K))
       (= B (+ 4 M))
       (not a!1)
       (<= F E)
       (= A (store L K (select L M)))))
      )
      (INV_MAIN_42 D E F G H C I J B A)
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
