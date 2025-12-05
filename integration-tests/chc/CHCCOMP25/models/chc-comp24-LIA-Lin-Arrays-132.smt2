(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |END_QUERY| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (v_10 Int) ) 
    (=>
      (and
        (and (= B (+ (- 4) G))
     (= A (+ (- 4) I))
     (= E I)
     (= D H)
     (= C G)
     (= F J)
     (= 0 v_10))
      )
      (INV_MAIN_42 C v_10 D E F B H A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A E F B H C G D I)
        (and (<= G 0) (<= F E) (not (= H I)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) ) 
    (=>
      (and
        (INV_MAIN_42 H K G J I M L O N)
        (let ((a!1 (= A (store N (+ 4 M) (select N (+ 4 O)))))
      (a!2 (store I (+ H (* 4 K)) (select I (+ J (* 4 K))))))
  (and a!1
       (= F (+ 1 K))
       (= D (+ 4 M))
       (= C (+ (- 1) L))
       (= B (+ 4 O))
       (not (<= G K))
       (not (<= L 0))
       (= E a!2)))
      )
      (INV_MAIN_42 H F G J E D C B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D G C F E H I J K)
        (let ((a!1 (store E (+ D (* 4 G)) (select E (+ F (* 4 G))))))
  (and (= B (+ 1 G)) (not (<= C G)) (<= I 0) (= A a!1)))
      )
      (INV_MAIN_42 D B C F A H I J K)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L (Array Int Int)) (M Int) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I K J M L)
        (let ((a!1 (= A (store L (+ 4 K) (select L (+ 4 M))))))
  (and (= C (+ (- 1) J))
       (= D (+ 4 K))
       (= B (+ 4 M))
       (not (<= J 0))
       (<= G F)
       a!1))
      )
      (INV_MAIN_42 E F G H I D C B A)
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
