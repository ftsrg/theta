(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (and (= A (+ F G)) (= D H) (= C F) (= B G) (= E I) (= 0 v_9) (= 0 v_10))
      )
      (INV_MAIN_42 v_9 v_10 B C D E F A H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C E F I G D H J)
        (let ((a!1 (= (+ (select J G) (* (- 1) (select J H))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select I E) (* (- 1) (select I F)))
              (+ (select J G) (* (- 1) (select J H))))))
  (and (not a!1)
       (not (= G D))
       a!2
       (or (not a!3) (not (= I J)))
       (= (select I E) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C G H I F D E J)
        (let ((a!1 (= (+ (select J F) (* (- 1) (select J E))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select I G) (* (- 1) (select I H))) 0)))
  (and (= (select J F) 0)
       a!1
       (not (= F D))
       a!2
       (or (not (= I J)) (not a!3))
       (= (select I G) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B D G H I E F C J)
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) 0)))
      (a!2 (= (+ (select I G) (* (- 1) (select I H))) 0)))
  (and (= E F) a!1 (or (not (= I J)) (not a!2)) (= (select I G) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C E F I G D H J)
        (let ((a!1 (= (+ (select J G) (* (- 1) (select J H))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select I E) (* (- 1) (select I F)))
              (+ (select J G) (* (- 1) (select J H))))))
  (and (not (= (select I E) 0))
       (not a!1)
       (not (= G D))
       a!2
       (or (not a!3) (not (= I J)))
       (not (= (select I E) (select I F)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C G H I F D E J)
        (let ((a!1 (= (+ (select J F) (* (- 1) (select J E))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select I G) (* (- 1) (select I H))) 0)))
  (and (not (= (select I G) 0))
       (= (select J F) 0)
       a!1
       (not (= F D))
       a!2
       (or (not (= I J)) (not a!3))
       (not (= (select I G) (select I H)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B D G H I E F C J)
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) 0)))
      (a!2 (= (+ (select I G) (* (- 1) (select I H))) 0)))
  (and (not (= (select I G) 0))
       (= E F)
       a!1
       (or (not (= I J)) (not a!2))
       (not (= (select I G) (select I H)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F C A B I G D H J)
        (let ((a!1 (= (+ E (* (- 1) F)) (+ (select J G) (* (- 1) (select J H)))))
      (a!2 (= (+ (select J G) (* (- 1) (select J H))) 0)))
  (and (not (= G D))
       (<= (ite (>= C 0) C (* (- 1) C)) 0)
       (or (not (= I J)) (not a!1))
       (not a!2)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 G H C A B I F D E J)
        (let ((a!1 (= (+ (select J F) (* (- 1) (select J E))) 0))
      (a!2 (not (= (+ G (* (- 1) H)) 0))))
  (and a!1
       (not (= F D))
       (<= (ite (>= C 0) C (* (- 1) C)) 0)
       (or (not (= I J)) a!2)
       (= (select J F) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 G H D A B I E F C J)
        (let ((a!1 (not (= (+ G (* (- 1) H)) 0))))
  (and (<= (ite (>= D 0) D (* (- 1) D)) 0) (or (not (= I J)) a!1) (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P Int) (Q (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 H I J K L M N O P Q)
        (let ((a!1 (= (+ (select Q N) (* (- 1) (select Q P))) 0))
      (a!2 (not (<= (ite (>= J 0) J (* (- 1) J)) 0))))
  (and (= (select M K) (select M L))
       (not (= (select M K) 0))
       a!1
       (= G (select M K))
       (not (= N O))
       (= F (select M L))
       (= E (+ (- 1) J))
       (= D (+ 1 K))
       (= C (+ 1 L))
       (= B (+ 1 N))
       (= A (+ 1 P))
       a!2
       (not (= (select Q N) 0))))
      )
      (INV_MAIN_42 G F E D C M B O A Q)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) (N Int) (O (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F G H I J K L M N O)
        (let ((a!1 (not (<= (ite (>= H 0) H (* (- 1) H)) 0)))
      (a!2 (= (+ (select O L) (* (- 1) (select O N))) 0)))
  (and (not (= (select K I) 0))
       (= E (select K I))
       (= D (select K J))
       (= C (+ (- 1) H))
       (= B (+ 1 I))
       (= A (+ 1 J))
       a!1
       (or (= L M) (not a!2) (= (select O L) 0))
       (= (select K I) (select K J))))
      )
      (INV_MAIN_42 E D C B A K L M N O)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J K L)
        (let ((a!1 (= (+ (select L I) (* (- 1) (select L K))) 0))
      (a!2 (or (<= (ite (>= E 0) E (* (- 1) E)) 0)
               (= (select H F) 0)
               (not (= (select H F) (select H G))))))
  (and a!1
       (= B (+ 1 I))
       (not (= I J))
       (= A (+ 1 K))
       a!2
       (not (= (select L I) 0))))
      )
      (INV_MAIN_42 C D E F G H B J A L)
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
