(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (select E (+ (- 1) F G)) H)))
      (a!2 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and (= (select A (+ (- 1) B C)) D)
       a!1
       (= D H)
       (not (= C 0))
       (= C G)
       (= B F)
       a!2
       (= A E)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (select E (+ (- 1) F G)) H)))
      (a!2 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and a!1 (= D 0) (= D G) (= B H) (= A F) a!2 (= C E)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (select A (+ (- 1) B C)) D)))
      (a!2 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and a!1
       (= (select E (+ (- 1) F G)) H)
       (= D H)
       (not (= C 0))
       (= C G)
       (= B F)
       a!2
       (= A E)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (select D (+ (- 1) E F)) G))))
  (and a!1
       (= G B)
       (not (= F 0))
       (= F H)
       (= E A)
       (<= (ite (>= H 0) H (* (- 1) H)) 0)
       (= D C)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) 0)))
      (a!2 (or (not (= (+ C D) (+ E F))) (not (= G H)))))
  (and (= (select G (+ (- 1) C D)) A)
       (= (select H (+ (- 1) E F)) B)
       (not (= D 0))
       (= D F)
       (= C E)
       (= A B)
       a!1
       a!2
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
        (let ((a!1 (or (not (= G H)) (not (= (+ E F) 1)))))
  (and (= (select G (+ (- 1) E F)) C)
       (not (= F 0))
       (= F D)
       (= E A)
       (= C B)
       (<= (ite (>= D 0) D (* (- 1) D)) 0)
       a!1
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
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) 0)))
      (a!2 (or (not (= G H)) (not (= 1 (+ E F))))))
  (and (= (select H (+ (- 1) E F)) D)
       (= C 0)
       (= C F)
       (= B D)
       (= A E)
       a!1
       a!2
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (= (select K (+ (- 1) I J)) H)))
      (a!2 (not (= (select G (+ (- 1) E F)) D)))
      (a!3 (not (<= (ite (>= J 0) J (* (- 1) J)) 0))))
  (and a!1
       a!2
       (= B (+ (- 1) J))
       (= A (+ (- 1) I J))
       (not (= F 0))
       (= F J)
       (= E I)
       (= D H)
       (= C (+ (- 1) E F))
       a!3
       (= G K)))
      )
      (INV_MAIN_0 D C F G H B A K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 B E A G D C F H)
        (let ((a!1 (not (<= (ite (>= C 0) C (* (- 1) C)) 0))))
  (and (= (select H (+ (- 1) F)) D)
       (not (= A 1))
       a!1
       (or (not (= G H)) (not (= E F)))
       (= (select G (+ (- 1) E)) B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D F C G A E B H)
        (and (not (= C 1))
     (<= (ite (>= E 0) E (* (- 1) E)) 0)
     (or (not (= G H)) (not (= F 1)))
     (= (select G (+ (- 1) F)) D))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C G E D F H)
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) 0))))
  (and (= C 1)
       a!1
       (or (not (= G H)) (not (= 1 F)))
       (= (select H (+ (- 1) F)) E)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B E G C F D H)
        (and (= E 1) (<= (ite (>= F 0) F (* (- 1) F)) 0) (not (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 E F G H I J K L)
        (let ((a!1 (not (= (select H (+ (- 1) F)) E)))
      (a!2 (not (<= (ite (>= J 0) J (* (- 1) J)) 0)))
      (a!3 (not (= (select L (+ (- 1) K)) I))))
  (and a!1
       (= C (+ (- 1) G))
       (= B (+ (- 1) J))
       (not (= G 1))
       (= D (+ (- 1) F))
       (= A (+ (- 1) K))
       a!2
       a!3))
      )
      (INV_MAIN_0 E D C H I B A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 C D E F G H I J)
        (let ((a!1 (or (<= (ite (>= H 0) H (* (- 1) H)) 0) (= (select J (+ (- 1) I)) G)))
      (a!2 (not (= (select F (+ (- 1) D)) C))))
  (and (= A (+ (- 1) E)) (not (= E 1)) (= B (+ (- 1) D)) a!1 a!2))
      )
      (INV_MAIN_0 C B A F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 C D E F G H I J)
        (let ((a!1 (not (<= (ite (>= H 0) H (* (- 1) H)) 0)))
      (a!2 (or (= E 1) (= (select F (+ (- 1) D)) C)))
      (a!3 (not (= (select J (+ (- 1) I)) G))))
  (and (= A (+ (- 1) I)) (= B (+ (- 1) H)) a!1 a!2 a!3))
      )
      (INV_MAIN_0 C D E F G B A J)
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
