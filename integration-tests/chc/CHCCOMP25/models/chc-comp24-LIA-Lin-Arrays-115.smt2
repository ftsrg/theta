(set-logic HORN)


(declare-fun |INV_MAIN_1| ( Int Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)
(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F) (= v_6 B) (= 0 v_7))
      )
      (INV_MAIN_0 B A v_6 C v_7 D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (INV_MAIN_0 E C A D B H F G)
        (and (= (select D C) (select D E))
     (not (= (select G H) 0))
     (not (= (select G F) (select G H)))
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
        (INV_MAIN_0 E A B D C H F G)
        (and (not (= (select G H) 0))
     (not (= (select G F) (select G H)))
     (not (= (select G F) 0))
     (= (select D E) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (INV_MAIN_0 C E A D B H F G)
        (and (not (= (select D E) 0))
     (not (= (select D C) 0))
     (not (= (select G H) 0))
     (= (select G F) (select G H))
     (not (= (select G F) 0))
     (not (= (select D E) (select D C))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (INV_MAIN_0 D F A E B C H G)
        (and (not (= (select E F) (select E D)))
     (not (= (select E F) 0))
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
        (INV_MAIN_0 D A E G F C B H)
        (let ((a!1 (not (= (+ D (* (- 1) E)) F))))
  (and (not (= (select G D) 0))
       (= (select H B) (select H C))
       (not (= (select H B) 0))
       (not (= (select H C) 0))
       (or a!1 (not (= G H)))
       (= (select G A) (select G D))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 E C F G A B D H)
        (let ((a!1 (not (= (+ E (* (- 1) F)) 0))))
  (and (= (select G C) (select G E))
       (= (select H D) 0)
       (or (not (= G H)) a!1)
       (not (= (select G E) 0))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 C A B G F E D H)
        (and (not (= (select H E) 0))
     (= (select H D) (select H E))
     (not (= (select H D) 0))
     (or (not (= G H)) (not (= 0 F)))
     (= (select G C) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 E A B G C D F H)
        (and (= (select G E) 0) (= (select H F) 0) (not (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I J K)
        (and (not (= (select G E) (select G D)))
     (= (select G E) 0)
     (not (= (select K J) 0))
     (= (select K I) 0)
     (= A (+ 1 J))
     (= B (+ 1 H))
     (= C (+ 1 D))
     (not (= (select G D) 0)))
      )
      (INV_MAIN_0 C E F G B I A K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 B C D E F G H I)
        (let ((a!1 (or (not (= (select I G) 0)) (= (select I H) 0))))
  (and (not (= (select E C) (select E B)))
       (= (select E C) 0)
       (= A (+ 1 B))
       a!1
       (not (= (select E B) 0))))
      )
      (INV_MAIN_0 A C D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 C D E F G H I J)
        (let ((a!1 (or (not (= (select F D) 0))
               (= (select F D) (select F C))
               (= (select F C) 0))))
  (and (= (select J H) 0)
       (= A (+ 1 I))
       (= B (+ 1 G))
       a!1
       (not (= (select J I) 0))))
      )
      (INV_MAIN_0 C D E F B H A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) (v_11 Int) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I J K)
        (and (not (= (select G E) (select G D)))
     (not (= (select G E) 0))
     (not (= (select K J) (select K I)))
     (not (= (select K J) 0))
     (not (= (select K I) 0))
     (= A (+ 1 E))
     (= B (+ 1 D))
     (= C (select G D))
     (not (= (select G D) 0))
     (= 0 v_11))
      )
      (INV_MAIN_1 C B A E F G v_11 H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) ) 
    (=>
      (and
        (INV_MAIN_1 H A G B C F K D J E I)
        (and (= (select I (+ 1 J K)) 0) (= (select F G) H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) ) 
    (=>
      (and
        (INV_MAIN_1 E A G B C F K D J H I)
        (let ((a!1 (not (= (select I (+ 1 J K)) 0))))
  (and (not (= (select F G) E))
       a!1
       (= (select I H) (select I (+ 1 J K)))
       (= (select F G) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C G B A H J F I E D K)
        (let ((a!1 (not (= (select K (+ 1 E F)) 0)))
      (a!2 (not (= (+ G (* (- 1) H)) (+ 1 I)))))
  (and a!1
       (= (select K D) (select K (+ 1 E F)))
       (or (not (= J K)) a!2)
       (= (select J B) C)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C F D G H I E J K L M)
        (and (not (= (select I D) C))
     (= (select M (+ 1 K E)) 0)
     (= B (+ 1 J))
     (= A (+ 1 L))
     (= (select I D) 0))
      )
      (INV_MAIN_0 F G H I B K A M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J K L M)
        (let ((a!1 (not (= (select M (+ 1 K I)) 0)))
      (a!2 (not (= (select M L) (select M (+ 1 K I))))))
  (and (not (= (select H E) C))
       a!1
       a!2
       (= B (+ 1 E))
       (= A (+ 1 I))
       (not (= (select H E) 0))))
      )
      (INV_MAIN_1 C D B F G H A J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I J K L)
        (let ((a!1 (or (= (select L K) (select L (+ 1 J H))) (= (select L (+ 1 J H)) 0))))
  (and (not (= (select G D) B)) (= A (+ 1 D)) a!1 (not (= (select G D) 0))))
      )
      (INV_MAIN_1 B C A E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I J K L)
        (let ((a!1 (not (= (select L K) (select L (+ 1 J H)))))
      (a!2 (not (= (select L (+ 1 J H)) 0))))
  (and a!1 (= A (+ 1 H)) (or (= (select G D) B) (= (select G D) 0)) a!2))
      )
      (INV_MAIN_1 B C D E F G A I J K L)
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
