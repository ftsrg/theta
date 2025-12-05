(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F B G C I A D H E J)
        (let ((a!1 (= (select I (+ F (* 4 G))) H)))
  (and (<= E D) (or (not a!1) (not (= I J))) (<= C B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F G H I J K L E M N)
        (let ((a!1 (>= (select J (+ F (* 4 G))) (select J (+ F (* 4 H)))))
      (a!2 (= A (select N (+ K (* 4 L)))))
      (a!3 (>= (select N (+ K (* 4 L))) E)))
  (and (= C (ite a!1 G H))
       (= B (+ 1 L))
       a!2
       a!3
       (not (<= M L))
       (not (<= I G))
       (= D (+ 1 G))))
      )
      (INV_MAIN_42 F D C I J K B A M N)
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
       (= A (+ 1 J))
       (not a!2)
       (not (<= G E))
       (not (<= L J))
       (= C (+ 1 E))))
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
        (let ((a!1 (>= (select G (+ C (* 4 D))) (select G (+ C (* 4 E)))))
      (a!2 (>= (select L (+ H (* 4 I))) J)))
  (and (= A (ite a!1 D E))
       (not (<= F D))
       (or (<= K I) a!2)
       (or (not a!2) (<= K I))
       (= B (+ 1 D))))
      )
      (INV_MAIN_42 C B A F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I J C K L)
        (let ((a!1 (= A (select L (+ I (* 4 J)))))
      (a!2 (>= (select L (+ I (* 4 J))) C)))
  (and a!1 a!2 (not (<= K J)) (<= G E) (= B (+ 1 J))))
      )
      (INV_MAIN_42 D E F G H I B A K L)
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
