(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (and (= A (+ F H)) (= D H) (= C G) (= B F) (= E I) (= 0 v_9) (= 0 v_10))
      )
      (INV_MAIN_42 v_9 v_10 D B C E F A G I)
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
       (= A (+ 1 P))
       (= B (+ 1 N))
       (= C (+ 1 L))
       (= D (+ 1 K))
       (= E (+ (- 1) J))
       (= F (select M L))
       (= G (select M K))
       (not (= N O))
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
       (= A (+ 1 J))
       (= B (+ 1 I))
       (= C (+ (- 1) H))
       (= D (select K J))
       (= E (select K I))
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
      (a!2 (or (= (select H F) 0)
               (not (= (select H F) (select H G)))
               (<= (ite (>= E 0) E (* (- 1) E)) 0))))
  (and a!1
       (= A (+ 1 K))
       (= B (+ 1 I))
       (not (= I J))
       a!2
       (not (= (select L I) 0))))
      )
      (INV_MAIN_42 C D E F G H B J A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (= (+ (select J G) (* (- 1) (select J I))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select F D) (* (- 1) (select F E)))
              (+ (select J G) (* (- 1) (select J I))))))
  (and (not a!1)
       (not (= G H))
       a!2
       (or (not a!3) (not (= F J)))
       (= (select F D) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (= (+ (select J G) (* (- 1) (select J I))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select F D) (* (- 1) (select F E))) 0)))
  (and (= (select F D) 0)
       a!1
       (not (= G H))
       a!2
       (or (not (= F J)) (not a!3))
       (= (select J G) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!2 (= (+ (select F D) (* (- 1) (select F E))) 0)))
  (and (= G H) a!1 (or (not (= F J)) (not a!2)) (= (select F D) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (= (+ (select J G) (* (- 1) (select J I))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select F D) (* (- 1) (select F E)))
              (+ (select J G) (* (- 1) (select J I))))))
  (and (not (= (select F D) 0))
       (not a!1)
       (not (= G H))
       a!2
       (or (not a!3) (not (= F J)))
       (not (= (select F D) (select F E)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (= (+ (select J G) (* (- 1) (select J I))) 0))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!3 (= (+ (select F D) (* (- 1) (select F E))) 0)))
  (and (not (= (select F D) (select F E)))
       (not (= (select F D) 0))
       a!1
       (not (= G H))
       a!2
       (or (not (= F J)) (not a!3))
       (= (select J G) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (not (<= (ite (>= C 0) C (* (- 1) C)) 0)))
      (a!2 (= (+ (select F D) (* (- 1) (select F E))) 0)))
  (and (not (= (select F D) 0))
       (= G H)
       a!1
       (or (not (= F J)) (not a!2))
       (not (= (select F D) (select F E)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (= (+ A (* (- 1) B)) (+ (select J G) (* (- 1) (select J I)))))
      (a!2 (= (+ (select J G) (* (- 1) (select J I))) 0)))
  (and (not (= G H))
       (<= (ite (>= C 0) C (* (- 1) C)) 0)
       (or (not (= F J)) (not a!1))
       (not a!2)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (= (+ (select J G) (* (- 1) (select J I))) 0))
      (a!2 (not (= (+ A (* (- 1) B)) 0))))
  (and a!1
       (not (= G H))
       (<= (ite (>= C 0) C (* (- 1) C)) 0)
       (or (not (= F J)) a!2)
       (= (select J G) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (not (= (+ A (* (- 1) B)) 0))))
  (and (<= (ite (>= C 0) C (* (- 1) C)) 0) (or (not (= F J)) a!1) (= G H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
