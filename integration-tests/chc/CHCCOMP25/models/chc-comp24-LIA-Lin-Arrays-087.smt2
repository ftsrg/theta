(set-logic HORN)


(declare-fun |INV_MAIN_0| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (= (select K (+ (- 1) H J)) I)))
      (a!2 (not (= (select G (+ (- 1) D F)) E)))
      (a!3 (not (<= (ite (>= J 0) J (* (- 1) J)) 0))))
  (and a!1
       a!2
       (= A (+ (- 1) H J))
       (= B (+ (- 1) J))
       (= C (+ (- 1) D F))
       (not (= F 0))
       (= F J)
       (= E I)
       (= D H)
       a!3
       (= G K)))
      )
      (INV_MAIN_0 E C F G I B A K)
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
       (= A (+ (- 1) K))
       (= B (+ (- 1) J))
       (= C (+ (- 1) G))
       (= D (+ (- 1) F))
       (not (= G 1))
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
  (and (= A (+ (- 1) E)) (= B (+ (- 1) D)) (not (= E 1)) a!1 a!2))
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
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (= (select H (+ (- 1) E G)) F)))
      (a!2 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and a!1
       (= (select D (+ (- 1) A C)) B)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       a!2
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (= (select H (+ (- 1) E G)) F)))
      (a!2 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and a!1 (= C 0) (= C G) (= B F) (= A E) a!2 (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (= (select D (+ (- 1) A C)) B)))
      (a!2 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and (= (select H (+ (- 1) E G)) F)
       a!1
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       a!2
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (= (select D (+ (- 1) A C)) B))))
  (and a!1
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (<= (ite (>= G 0) G (* (- 1) G)) 0)
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0)))
      (a!2 (or (not (= (+ A C) (+ E G))) (not (= D H)))))
  (and (= (select H (+ (- 1) E G)) F)
       (= (select D (+ (- 1) A C)) B)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       a!1
       a!2
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= D H)) (not (= (+ A C) 1)))))
  (and (= (select D (+ (- 1) A C)) B)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (<= (ite (>= G 0) G (* (- 1) G)) 0)
       a!1
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0)))
      (a!2 (or (not (= D H)) (not (= 1 (+ E G))))))
  (and (= (select H (+ (- 1) E G)) F)
       (= C 0)
       (= C G)
       (= B F)
       (= A E)
       a!1
       a!2
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) 0))))
  (and (= (select D (+ (- 1) B)) A)
       (not (= C 1))
       a!1
       (or (not (= D H)) (not (= B G)))
       (= (select H (+ (- 1) G)) E)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (and (not (= C 1))
     (<= (ite (>= F 0) F (* (- 1) F)) 0)
     (or (not (= D H)) (not (= B 1)))
     (= (select D (+ (- 1) B)) A))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) 0))))
  (and (= C 1)
       a!1
       (or (not (= D H)) (not (= 1 G)))
       (= (select H (+ (- 1) G)) E)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (and (= C 1) (<= (ite (>= F 0) F (* (- 1) F)) 0) (not (= D H)))
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
