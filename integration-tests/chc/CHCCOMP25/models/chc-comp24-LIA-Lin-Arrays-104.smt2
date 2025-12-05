(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (and (= D G)
     (= C F)
     (= B E)
     (>= B 0)
     (= A (store (store G F 1) (+ 4 F) 1))
     (= 1 v_7)
     (= 1 v_8)
     (= 2 v_9)
     (= 2 v_10))
      )
      (INV_MAIN_42 v_7 v_8 v_9 B D F v_10 E A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J K L M)
        (let ((a!1 (+ (select M (+ (- 4) J (* 4 K))) (select M (+ (- 8) J (* 4 K))))))
(let ((a!2 (= A (store M (+ J (* 4 K)) a!1))))
  (and (= B (+ 1 K))
       (= C (+ 1 G))
       (= D (+ F E))
       (not (<= L K))
       (not (<= H G))
       a!2)))
      )
      (INV_MAIN_42 F D C H I J B L A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J K)
        (and (= B (+ D C)) (<= J I) (not (<= F E)) (= A (+ 1 E)))
      )
      (INV_MAIN_42 D B A F G H I J K)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J K)
        (let ((a!1 (+ (select K (+ (- 4) H (* 4 I))) (select K (+ (- 8) H (* 4 I))))))
(let ((a!2 (= A (store K (+ H (* 4 I)) a!1))))
  (and (= B (+ 1 I)) (not (<= J I)) (<= F E) a!2)))
      )
      (INV_MAIN_42 C D E F G H B J A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I)
        (let ((a!1 (= B (select I (+ (- 4) F (* 4 G))))))
  (and (<= H G) (<= D C) (not a!1)))
      )
      false
    )
  )
)

(check-sat)
(exit)
