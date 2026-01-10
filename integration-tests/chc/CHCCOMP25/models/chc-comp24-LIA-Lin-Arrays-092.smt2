(set-logic HORN)


(declare-fun |INV_MAIN_1| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) (ite (>= F 0) F (* (- 1) F)))))
      (a!2 (not (<= (ite (>= C 0) C (* (- 1) C)) (ite (>= B 0) B (* (- 1) B))))))
  (and (= A (+ (- 1) H))
       (not (= H 0))
       (not (= G F))
       (not (= D 0))
       (= D H)
       (= C G)
       (= B F)
       (not (= B C))
       a!1
       a!2
       (= E I)
       (= v_9 B)
       (= v_10 F)))
      )
      (INV_MAIN_0 B v_9 C D E F G A v_10 I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (and (= A (+ (- 1) L))
     (= B (+ (- 1) K L))
     (= C (+ (- 1) J L))
     (= E (+ F H))
     (= D (+ G H))
     (not (= L 0))
     (not (= K J))
     (not (= H 0))
     (= H L)
     (= G K)
     (= F J)
     (not (= F G))
     (<= (ite (>= K 0) K (* (- 1) K)) (ite (>= J 0) J (* (- 1) J)))
     (<= (ite (>= G 0) G (* (- 1) G)) (ite (>= F 0) F (* (- 1) F)))
     (= I M))
      )
      (INV_MAIN_1 E F D H I C B A J M)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P Int) (Q Int) (R (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 I J K L M N O P Q R)
        (and (= E (store M I (select M K)))
     (= B (+ (- 1) P))
     (= C (+ 1 O))
     (= D (+ 1 N))
     (= F (+ (- 1) L))
     (= G (+ 1 K))
     (= H (+ 1 I))
     (not (= P 0))
     (not (= L 1))
     (= A (store R N (select R O))))
      )
      (INV_MAIN_0 H J G F E D C B Q A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 E F G H I J K L M N)
        (and (= B (+ (- 1) H))
     (= C (+ 1 G))
     (= D (+ 1 E))
     (= L 0)
     (not (= H 1))
     (= A (store I E (select I G))))
      )
      (INV_MAIN_0 D F C B A J K L M N)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 E F G H I J K L M N)
        (and (= B (+ (- 1) L))
     (= C (+ 1 K))
     (= D (+ 1 J))
     (not (= L 0))
     (= H 1)
     (= A (store N J (select N K))))
      )
      (INV_MAIN_0 E F G H I D C B M A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P Int) (Q Int) (R (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 I J K L M N O P Q R)
        (let ((a!1 (= E (store M (+ (- 1) I) (select M (+ (- 1) K))))))
  (and a!1
       (= B (+ (- 1) P))
       (= C (+ (- 1) O))
       (= D (+ (- 1) N))
       (= F (+ (- 1) L))
       (= G (+ (- 1) K))
       (= H (+ (- 1) I))
       (not (= P 0))
       (not (= L 1))
       (= A (store R N (select R O)))))
      )
      (INV_MAIN_1 H J G F E D C B Q A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L M N)
        (let ((a!1 (= A (store I (+ (- 1) E) (select I (+ (- 1) G))))))
  (and (= B (+ (- 1) H))
       (= C (+ (- 1) G))
       (= D (+ (- 1) E))
       (= L 0)
       (not (= H 1))
       a!1))
      )
      (INV_MAIN_1 D F C B A J K L M N)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L M N)
        (and (= B (+ (- 1) L))
     (= C (+ (- 1) K))
     (= D (+ (- 1) J))
     (not (= L 0))
     (= H 1)
     (= A (store N J (select N K))))
      )
      (INV_MAIN_1 E F G H I D C B M A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E))))))
  (and (not (= G 0))
       (not (= F E))
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (= C 0) (= A B))
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
        (and (not (= G 0))
     (not (= F E))
     (= C G)
     (= B F)
     (= A E)
     (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E)))
     (or (= C 0) (= A B))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E)))))
      (a!2 (not (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A))))))
  (and (= G 0)
       (not (= F E))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (not (= A B))
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
        (let ((a!1 (not (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A))))))
  (and (= G 0)
       (not (= F E))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (not (= A B))
       (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E)))
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
        (let ((a!1 (not (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A))))))
  (and (= F E) (not (= C 0)) (= C G) (= B F) (= A E) (not (= A B)) a!1 (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A))))))
  (and (not (= G 0))
       (not (= F E))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (not (= A B))
       (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E)))
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
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E))))))
  (and (= G 0)
       (not (= F E))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (not (= A B))
       a!1
       (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A)))
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
        (and (= G 0)
     (not (= F E))
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (not (= A B))
     (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E)))
     (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A)))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= F E)
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (not (= A B))
     (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A)))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E))))))
  (and (not (= G 0))
       (not (= F E))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (not (= A B))
       a!1
       (<= (ite (>= B 0) B (* (- 1) B)) (ite (>= A 0) A (* (- 1) A)))
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
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E))))))
  (and (= G 0)
       (not (= F E))
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (not (= D H)) (not (= A E)))
       (or (= C 0) (= A B))
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
        (and (= G 0)
     (not (= F E))
     (= C G)
     (= B F)
     (= A E)
     (<= (ite (>= F 0) F (* (- 1) F)) (ite (>= E 0) E (* (- 1) E)))
     (or (not (= D H)) (not (= A E)))
     (or (= C 0) (= A B))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= F E)
     (= C G)
     (= B F)
     (= A E)
     (or (not (= D H)) (not (= A E)))
     (or (= C 0) (= A B))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H I J)
        (let ((a!1 (not (= (store E A (select E C)) (store J F (select J G))))))
  (and (= D 1) (or (not (= B I)) a!1) (= H 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H I J)
        (let ((a!1 (= (store E (+ (- 1) A) (select E (+ (- 1) C)))
              (store J F (select J G)))))
  (and (= D 1) (or (not (= B I)) (not a!1)) (= H 0)))
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
