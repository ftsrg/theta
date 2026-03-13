(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |INV_MAIN_2| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F) (= 0 v_6) (= 0 v_7))
      )
      (INV_MAIN_1 A v_6 B C D v_7 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E F B C G H D)
        (and (<= F E) (not (<= H G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E F B C G H D)
        (and (not (<= F E)) (<= H G))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A C D G B E F H)
        (and (<= F E) (<= D C) (not (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (and (not (<= C B)) (not (<= G F)) (= v_8 B) (= v_9 F))
      )
      (INV_MAIN_2 A B v_8 C D E F v_9 G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_2 A B D E C I J G F H)
        (let ((a!1 (<= (select H (+ I (* 4 J))) (select H (+ I (* 4 G))))))
  (and (not (<= F G)) (<= E D) (not a!1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_2 A B D E C I J G F H)
        (let ((a!1 (<= (select H (+ I (* 4 J))) (select H (+ I (* 4 G))))))
  (and (not (<= F G)) (<= E D) a!1))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_2 G H E D F A B I J C)
        (let ((a!1 (<= (select F (+ G (* 4 E))) (select F (+ G (* 4 H))))))
  (and (not (<= D E)) (<= J I) a!1))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_2 G H E D F A B I J C)
        (let ((a!1 (<= (select F (+ G (* 4 E))) (select F (+ G (* 4 H))))))
  (and (not (<= D E)) (<= J I) (not a!1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 E F C G H I J D K L)
        (and (= A (+ 1 J)) (<= K D) (<= G C) (= B (+ 1 F)))
      )
      (INV_MAIN_1 E B G H I A K L)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) ) 
    (=>
      (and
        (INV_MAIN_2 H I F E G M N K J L)
        (let ((a!1 (store L (+ M (* 4 N)) (select L (+ M (* 4 K)))))
      (a!3 (<= (select G (+ H (* 4 F))) (select G (+ H (* 4 I)))))
      (a!4 (<= (select L (+ M (* 4 N))) (select L (+ M (* 4 K)))))
      (a!5 (store G (+ H (* 4 I)) (select G (+ H (* 4 F))))))
(let ((a!2 (store a!1 (+ M (* 4 K)) (select L (+ M (* 4 N)))))
      (a!6 (store a!5 (+ H (* 4 F)) (select G (+ H (* 4 I))))))
  (and (= A a!2)
       (= D (+ 1 F))
       (= B (+ 1 K))
       a!3
       (not a!4)
       (not (<= E F))
       (not (<= J K))
       (= C a!6))))
      )
      (INV_MAIN_2 H I D E C M N B J A)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 G H E D F I J K L M)
        (let ((a!1 (<= (select F (+ G (* 4 E))) (select F (+ G (* 4 H)))))
      (a!2 (<= (select M (+ I (* 4 J))) (select M (+ I (* 4 K)))))
      (a!3 (store F (+ G (* 4 H)) (select F (+ G (* 4 E))))))
(let ((a!4 (store a!3 (+ G (* 4 E)) (select F (+ G (* 4 H))))))
  (and (= C (+ 1 E))
       (= A (+ 1 K))
       a!1
       a!2
       (not (<= D E))
       (not (<= L K))
       (= B a!4))))
      )
      (INV_MAIN_2 G H C D B I J A L M)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) ) 
    (=>
      (and
        (INV_MAIN_2 D E F G H L M J I K)
        (let ((a!1 (<= (select H (+ D (* 4 F))) (select H (+ D (* 4 E)))))
      (a!2 (<= (select K (+ L (* 4 M))) (select K (+ L (* 4 J)))))
      (a!3 (store K (+ L (* 4 M)) (select K (+ L (* 4 J))))))
(let ((a!4 (store a!3 (+ L (* 4 J)) (select K (+ L (* 4 M))))))
  (and (= C (+ 1 F))
       (= B (+ 1 J))
       (not a!1)
       (not a!2)
       (not (<= G F))
       (not (<= I J))
       (= A a!4))))
      )
      (INV_MAIN_2 D E C G H L M B I A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H I J K L)
        (let ((a!1 (<= (select G (+ C (* 4 E))) (select G (+ C (* 4 D)))))
      (a!2 (<= (select L (+ H (* 4 I))) (select L (+ H (* 4 J))))))
  (and (= A (+ 1 J)) (not a!1) a!2 (not (<= F E)) (not (<= K J)) (= B (+ 1 E))))
      )
      (INV_MAIN_2 C D B F G H I A K L)
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
