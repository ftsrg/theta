(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G))))))
  (and (= D G)
       (not (= H 0))
       (not (= F G))
       (= E F)
       (= C H)
       a!1
       (or (= D E) (= C 0))
       (= A B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= D G)
     (not (= H 0))
     (not (= F G))
     (= E F)
     (= C H)
     (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G)))
     (or (= D E) (= C 0))
     (= A B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) (ite (>= C 0) C (* (- 1) C)))))
      (a!2 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G))))))
  (and (= D F)
       (= H 0)
       (not (= F G))
       (not (= E 0))
       (= E H)
       (not (= C D))
       (= C G)
       a!1
       a!2
       (= A B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) (ite (>= C 0) C (* (- 1) C))))))
  (and (= D F)
       (= H 0)
       (not (= F G))
       (not (= E 0))
       (= E H)
       (not (= C D))
       (= C G)
       a!1
       (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G)))
       (= A B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= E 0) E (* (- 1) E)) (ite (>= D 0) D (* (- 1) D))))))
  (and (= D H) (not (= D E)) (= G H) (not (= F 0)) (= F A) (= E G) a!1 (= B C)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) (ite (>= C 0) C (* (- 1) C))))))
  (and (= D F)
       (not (= H 0))
       (not (= F G))
       (not (= E 0))
       (= E H)
       (not (= C D))
       (= C G)
       a!1
       (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G)))
       (= A B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G))))))
  (and (= D F)
       (= H 0)
       (not (= F G))
       (not (= E 0))
       (= E H)
       (not (= C D))
       (= C G)
       (<= (ite (>= D 0) D (* (- 1) D)) (ite (>= C 0) C (* (- 1) C)))
       a!1
       (= A B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= D F)
     (= H 0)
     (not (= F G))
     (not (= E 0))
     (= E H)
     (not (= C D))
     (= C G)
     (<= (ite (>= D 0) D (* (- 1) D)) (ite (>= C 0) C (* (- 1) C)))
     (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G)))
     (= A B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= D H)
     (not (= D E))
     (= G H)
     (not (= F 0))
     (= F A)
     (= E G)
     (<= (ite (>= E 0) E (* (- 1) E)) (ite (>= D 0) D (* (- 1) D)))
     (= B C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= G 0) G (* (- 1) G))))))
  (and (= D F)
       (not (= H 0))
       (not (= F G))
       (not (= E 0))
       (= E H)
       (not (= C D))
       (= C G)
       (<= (ite (>= D 0) D (* (- 1) D)) (ite (>= C 0) C (* (- 1) C)))
       a!1
       (= A B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= C 0) C (* (- 1) C)) (ite (>= F 0) F (* (- 1) F))))))
  (and (= D 0)
       (= E F)
       (not (= C F))
       (= B C)
       (= A D)
       a!1
       (or (not (= E F)) (not (= G H)))
       (or (= E B) (= A 0))
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= D 0)
     (= E F)
     (not (= C F))
     (= B C)
     (= A D)
     (<= (ite (>= C 0) C (* (- 1) C)) (ite (>= F 0) F (* (- 1) F)))
     (or (not (= E F)) (not (= G H)))
     (or (= E B) (= A 0))
     (= G H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= D F)
     (= E F)
     (= C D)
     (= B A)
     (or (not (= E F)) (not (= G H)))
     (or (= E C) (= B 0))
     (= G H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= H 0) H (* (- 1) H)))))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) (ite (>= B 0) B (* (- 1) B))))))
  (and (= A (+ (- 1) G))
       (not (= G 0))
       (not (= F H))
       (not (= D 0))
       (= D G)
       (= C F)
       (= B H)
       (not (= B C))
       a!1
       a!2
       (= E I)
       (= v_9 B)
       (= v_10 H)))
      )
      (INV_MAIN_0 B v_9 C D E H F A v_10 I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (and (= D (+ G H))
     (= E (+ F H))
     (not (= K 0))
     (not (= J L))
     (not (= H 0))
     (= H K)
     (= G J)
     (= F L)
     (not (= F G))
     (= C (+ (- 1) L K))
     (= B (+ (- 1) J K))
     (= A (+ (- 1) K))
     (<= (ite (>= J 0) J (* (- 1) J)) (ite (>= L 0) L (* (- 1) L)))
     (<= (ite (>= G 0) G (* (- 1) G)) (ite (>= F 0) F (* (- 1) F)))
     (= I M))
      )
      (INV_MAIN_1 E F D H I C B A L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (INV_MAIN_0 E C G A F H J B D I)
        (let ((a!1 (not (= (store F E (select F G)) (store I H (select I J))))))
  (and (= B 0) (or (not (= C D)) a!1) (= A 1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) (O Int) (P Int) (Q (Array Int Int)) (R Int) ) 
    (=>
      (and
        (INV_MAIN_0 K I M J L P R N O Q)
        (and (= E (store L K (select L M)))
     (= C (+ 1 R))
     (= D (+ 1 P))
     (= B (+ (- 1) N))
     (not (= J 1))
     (not (= N 0))
     (= H (+ 1 K))
     (= G (+ 1 M))
     (= F (+ (- 1) J))
     (= A (store Q P (select Q R))))
      )
      (INV_MAIN_0 H I G F E D C B O A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 G E I F H J K L M N)
        (and (not (= F 1))
     (= L 0)
     (= D (+ 1 G))
     (= C (+ 1 I))
     (= B (+ (- 1) F))
     (= A (store H G (select H I))))
      )
      (INV_MAIN_0 D E C B A J K L M N)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) ) 
    (=>
      (and
        (INV_MAIN_0 E F G H I L N J K M)
        (and (not (= J 0))
     (= H 1)
     (= D (+ 1 L))
     (= C (+ 1 N))
     (= B (+ (- 1) J))
     (= A (store M L (select M N))))
      )
      (INV_MAIN_0 E F G H I D C B K A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (INV_MAIN_1 E C G A F H J B D I)
        (let ((a!1 (= (store F (+ (- 1) E) (select F (+ (- 1) G)))
              (store I H (select I J)))))
  (and (= B 0) (or (not (= C D)) (not a!1)) (= A 1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) (O Int) (P Int) (Q (Array Int Int)) (R Int) ) 
    (=>
      (and
        (INV_MAIN_1 K I M J L P R N O Q)
        (let ((a!1 (= E (store L (+ (- 1) K) (select L (+ (- 1) M))))))
  (and a!1
       (= C (+ (- 1) R))
       (= D (+ (- 1) P))
       (= B (+ (- 1) N))
       (not (= J 1))
       (not (= N 0))
       (= H (+ (- 1) K))
       (= G (+ (- 1) M))
       (= F (+ (- 1) J))
       (= A (store Q P (select Q R)))))
      )
      (INV_MAIN_1 H I G F E D C B O A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 G E I F H J K L M N)
        (let ((a!1 (= A (store H (+ (- 1) G) (select H (+ (- 1) I))))))
  (and (not (= F 1))
       (= L 0)
       (= D (+ (- 1) G))
       (= C (+ (- 1) I))
       (= B (+ (- 1) F))
       a!1))
      )
      (INV_MAIN_1 D E C B A J K L M N)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I L N J K M)
        (and (not (= J 0))
     (= H 1)
     (= D (+ (- 1) L))
     (= C (+ (- 1) N))
     (= B (+ (- 1) J))
     (= A (store M L (select M N))))
      )
      (INV_MAIN_1 E F G H I D C B K A)
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
