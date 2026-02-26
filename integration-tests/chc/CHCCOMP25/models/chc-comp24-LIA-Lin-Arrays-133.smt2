(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int Int (Array Int Int) Int Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (v_7 Int) (v_8 Int) ) 
    (=>
      (and
        (and (= C F)
     (= B E)
     (not (<= B 0))
     (= (select D A) (select G A))
     (= 0 v_7)
     (= 0 v_8))
      )
      (INV_MAIN_1 v_7 B C D v_8 E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) ) 
    (=>
      (and
        (INV_MAIN_0 A H G E F J B C D K I)
        (let ((a!1 (not (= (select F (+ 1 G H)) 0))))
  (and (= (select F E) (select F (+ 1 G H)))
       (= (select I (+ 1 K)) J)
       (= K (- 1))
       a!1))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) ) 
    (=>
      (and
        (INV_MAIN_0 A H G E F I B C D K J)
        (let ((a!1 (not (= (select J (+ 1 K)) I)))
      (a!2 (not (= (select F (+ 1 G H)) 0))))
  (and a!1 a!2 (= (select F E) (select F (+ 1 G H))) (= (select J (+ 1 K)) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) ) 
    (=>
      (and
        (INV_MAIN_0 A H G B F J C D E K I)
        (and (= (select I (+ 1 K)) J) (not (= K (- 1))) (= (select F (+ 1 G H)) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 H E D C J F I A B G K)
        (let ((a!1 (not (= (select J (+ 1 D E)) 0))))
  (and (= (select J C) (select J (+ 1 D E)))
       (= (select K (+ 1 G)) F)
       (not (= G (- 1)))
       (or (not (= H I)) (not (= J K)))
       a!1))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 C D E F G H I J K L M)
        (let ((a!1 (not (= (select G F) (select G (+ 1 E D)))))
      (a!2 (not (= (select M (+ 1 L)) 0)))
      (a!3 (not (= (select M (+ 1 L)) H)))
      (a!4 (not (= (select G (+ 1 E D)) 0))))
  (and a!1 a!2 a!3 (= A (+ 1 L)) (= B (+ 1 D)) a!4))
      )
      (INV_MAIN_0 C B E F G H I J K A M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 B C D E F G H I J K L)
        (let ((a!1 (not (= (select F E) (select F (+ 1 D C)))))
      (a!2 (or (= (select L (+ 1 K)) G) (= (select L (+ 1 K)) 0)))
      (a!3 (not (= (select F (+ 1 D C)) 0))))
  (and a!1 (= A (+ 1 C)) a!2 a!3))
      )
      (INV_MAIN_0 B A D E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 B C D E F G H I J K L)
        (let ((a!1 (not (= (select L (+ 1 K)) G)))
      (a!2 (or (= (select F E) (select F (+ 1 D C))) (= (select F (+ 1 D C)) 0)))
      (a!3 (not (= (select L (+ 1 K)) 0))))
  (and a!1 (= A (+ 1 K)) a!2 a!3))
      )
      (INV_MAIN_0 B C D E F G H I J A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 G D H I J E K M L F N)
        (and (= (select N (+ 1 F)) E)
     (= F (- 1))
     (= B (+ 1 I))
     (= C (+ 1 G))
     (= A (+ 1 K))
     (= (select J (+ 1 H D)) 0))
      )
      (INV_MAIN_1 C H B J A L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 G D H I J E K M L F N)
        (let ((a!1 (not (= (select N (+ 1 F)) E))))
  (and (= (select N (+ 1 F)) 0)
       a!1
       (= B (+ 1 I))
       (= C (+ 1 G))
       (= A (+ 1 K))
       (= (select J (+ 1 H D)) 0)))
      )
      (INV_MAIN_1 C H B J A L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E C D B H F G)
        (and (= (select D C) (select D E))
     (not (= (select D C) 0))
     (not (= (select G H) (select G F)))
     (not (= (select G H) 0))
     (not (= (select G F) 0))
     (not (= (select D E) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A B E D C H F G)
        (and (not (= (select G H) (select G F)))
     (not (= (select G H) 0))
     (not (= (select G F) 0))
     (= (select D E) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E C D B H G F)
        (and (not (= (select D C) (select D E)))
     (not (= (select D C) 0))
     (= (select F H) (select F G))
     (not (= (select F G) 0))
     (not (= H 0))
     (not (= (select D E) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A F D E B C H G)
        (and (not (= (select E F) 0))
     (not (= (select E D) (select E F)))
     (not (= (select E D) 0))
     (= (select G H) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E B A G F D C H)
        (and (not (= (select G A) 0))
     (not (= (select G B) 0))
     (= (select H D) (select H C))
     (not (= (select H C) 0))
     (not (= D 0))
     (or (not (= E F)) (not (= G H)))
     (= (select G A) (select G B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E C B G F A D H)
        (and (not (= (select G B) 0))
     (not (= (select G C) 0))
     (= (select H D) 0)
     (or (not (= E F)) (not (= G H)))
     (= (select G B) (select G C)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E A B G F D C H)
        (and (= (select H D) (select H C))
     (not (= (select H C) 0))
     (not (= D 0))
     (or (not (= E F)) (not (= G H)))
     (= (select G B) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E A C G F B D H)
        (and (= (select H D) 0) (or (not (= E F)) (not (= G H))) (= (select G C) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (v_10 Int) (v_11 Int) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G I H J)
        (and (not (= (select F E) (select F D)))
     (not (= (select F E) 0))
     (not (= (select J I) (select J H)))
     (not (= (select J I) 0))
     (not (= (select J H) 0))
     (= A (+ 1 H))
     (= B (select J H))
     (not (= (select F D) 0))
     (= 0 v_10)
     (= v_11 I))
      )
      (INV_MAIN_0 C v_10 D E F B G A I v_11 J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L)
        (and (not (= (select H G) 0))
     (not (= (select L K) 0))
     (= (select L J) (select L K))
     (= B (+ 1 I))
     (= C (+ 1 G))
     (= D (+ 1 E))
     (= A (+ 1 K))
     (= J 0)
     (= (select H F) 0))
      )
      (INV_MAIN_1 D F C H B J A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L)
        (and (not (= (select H G) 0))
     (not (= (select L K) 0))
     (not (= (select L J) (select L K)))
     (= (select L J) 0)
     (= B (+ 1 I))
     (= C (+ 1 G))
     (= D (+ 1 E))
     (= A (+ 1 K))
     (= (select H F) 0))
      )
      (INV_MAIN_1 D F C H B J A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J)
        (let ((a!1 (or (= (select J H) (select J I))
               (not (= (select J H) 0))
               (= (select J I) 0)))
      (a!2 (or (not (= H 0))
               (not (= (select J H) (select J I)))
               (= (select J I) 0))))
  (and (not (= (select F E) 0))
       (= A (+ 1 E))
       (= B (+ 1 C))
       a!1
       a!2
       (= (select F D) 0)))
      )
      (INV_MAIN_1 B D A F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J)
        (let ((a!1 (or (= (select F E) 0) (not (= (select F D) 0)))))
  (and (= (select J H) (select J I))
       (= A (+ 1 I))
       (= B (+ 1 G))
       (= H 0)
       a!1
       (not (= (select J I) 0))))
      )
      (INV_MAIN_1 C D E F B H A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J)
        (let ((a!1 (or (= (select F E) 0) (not (= (select F D) 0)))))
  (and (not (= (select J H) (select J I)))
       (= (select J H) 0)
       (= A (+ 1 I))
       (= B (+ 1 G))
       a!1
       (not (= (select J I) 0))))
      )
      (INV_MAIN_1 C D E F B H A J)
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
