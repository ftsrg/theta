(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (v_7 Int) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (and (= A (select G E)) (= C F) (= B E) (= D G) (= 1 v_7) (= 0 v_8) (= 1 v_9))
      )
      (INV_MAIN_42 B v_7 v_8 C D E v_9 A F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J K L M N)
        (let ((a!1 (>= (select I (+ E (* 4 F))) (select I (+ E (* 4 G)))))
      (a!2 (>= (select N (+ J (* 4 K))) L))
      (a!3 (= A (select N (+ J (* 4 K))))))
  (and (= B (+ 1 K))
       (= C (ite a!1 F G))
       (= D (+ 1 F))
       a!2
       (not (<= H F))
       (not (<= M K))
       a!3))
      )
      (INV_MAIN_42 E D C H I J B A M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I J K L M)
        (let ((a!1 (>= (select H (+ D (* 4 E))) (select H (+ D (* 4 F)))))
      (a!2 (>= (select M (+ I (* 4 J))) K)))
  (and (= B (ite a!1 E F))
       (= C (+ 1 E))
       (not a!2)
       (not (<= G E))
       (not (<= L J))
       (= A (+ 1 J))))
      )
      (INV_MAIN_42 D C B G H I A K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J K L)
        (let ((a!1 (>= (select L (+ H (* 4 I))) J))
      (a!2 (>= (select G (+ C (* 4 D))) (select G (+ C (* 4 E))))))
  (and (= B (+ 1 D))
       (not (<= F D))
       (or (<= K I) a!1)
       (or (not a!1) (<= K I))
       (= A (ite a!2 D E))))
      )
      (INV_MAIN_42 C B A F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J K L)
        (let ((a!1 (>= (select L (+ H (* 4 I))) J))
      (a!2 (= A (select L (+ H (* 4 I))))))
  (and (= B (+ 1 I)) a!1 (<= F D) (not (<= K I)) a!2))
      )
      (INV_MAIN_42 C D E F G H B A K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 B C D E F G H I J K)
        (let ((a!1 (>= (select K (+ G (* 4 H))) I)))
  (and (not a!1) (<= E C) (not (<= J H)) (= A (+ 1 H))))
      )
      (INV_MAIN_42 B C D E F G A I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (= (select E (+ A (* 4 C))) H)))
  (and (<= I G) (or (not a!1) (not (= E J))) (<= D B)))
      )
      false
    )
  )
)

(check-sat)
(exit)
