(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |END_QUERY| ( ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (and (= D F)
     (= C E)
     (= B G)
     (>= C 0)
     (= A (store (store F G 1) (+ 4 G) 1))
     (= 1 v_7)
     (= 1 v_8)
     (= 2 v_9)
     (= 2 v_10))
      )
      (INV_MAIN_42 v_7 v_8 v_9 C D G v_10 E A)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 A F C D B H I E G)
        (let ((a!1 (= F (select G (+ (- 4) H (* 4 I))))))
  (and (<= E I) (<= D C) (not a!1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K (Array Int Int)) (L Int) (M Int) ) 
    (=>
      (and
        (INV_MAIN_42 F E G H I L M J K)
        (let ((a!1 (+ (select K (+ (- 4) L (* 4 M))) (select K (+ (- 8) L (* 4 M))))))
(let ((a!2 (= A (store K (+ L (* 4 M)) a!1))))
  (and (= D (+ E F))
       (= C (+ 1 G))
       (= B (+ 1 M))
       (not (<= J M))
       (not (<= H G))
       a!2)))
      )
      (INV_MAIN_42 E D C H I L B J A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D C E F G H I J K)
        (and (= A (+ 1 E)) (<= J I) (not (<= F E)) (= B (+ C D)))
      )
      (INV_MAIN_42 C B A F G H I J K)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I (Array Int Int)) (J Int) (K Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G J K H I)
        (let ((a!1 (+ (select I (+ (- 4) J (* 4 K))) (select I (+ (- 8) J (* 4 K))))))
(let ((a!2 (= A (store I (+ J (* 4 K)) a!1))))
  (and (= B (+ 1 K)) (not (<= H K)) (<= F E) a!2)))
      )
      (INV_MAIN_42 C D E F G J B H A)
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
