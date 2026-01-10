(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= M 0) M (* (- 1) M)) 0))))
  (and (= (select N K) (select N L))
       (not (= (select N K) 0))
       (= (select J G) (select J H))
       (not (= (select J G) 0))
       (= A (+ 1 L))
       (= B (+ 1 K))
       (= C (select N L))
       (= D (select N K))
       (= F (+ 1 H))
       (= E (+ 1 G))
       (not (= I 0))
       (= I M)
       (= H L)
       (= G K)
       a!1
       (= J N)))
      )
      (INV_MAIN_42 F E I J D C B A M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) (O Int) (P Int) (Q Int) (R (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 I J K L M N O P Q R)
        (let ((a!1 (<= (ite (>= Q 1) (+ (- 1) Q) (+ 1 (* (- 1) Q))) 0)))
  (and (not (= (select L J) 0))
       (= (select R O) (select R P))
       (not (= (select R O) 0))
       (= A (+ (- 1) Q))
       (= B (+ 1 P))
       (= C (+ 1 O))
       (= D (select R P))
       (= E (select R O))
       (= F (+ (- 1) K))
       (= G (+ 1 J))
       (= H (+ 1 I))
       (not (= K 1))
       (not a!1)
       (= (select L J) (select L I))))
      )
      (INV_MAIN_42 H G F L E D C B A R)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I J K L M)
        (let ((a!1 (<= (ite (>= L 1) (+ (- 1) L) (+ 1 (* (- 1) L))) 0)))
(let ((a!2 (or (= (select M J) 0) (not (= (select M J) (select M K))) a!1)))
  (and (not (= (select G E) 0))
       (= A (+ (- 1) F))
       (= B (+ 1 E))
       (= C (+ 1 D))
       (not (= F 1))
       a!2
       (= (select G E) (select G D)))))
      )
      (INV_MAIN_42 C B A G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F G H I J K L M N O)
        (let ((a!1 (<= (ite (>= N 1) (+ (- 1) N) (+ 1 (* (- 1) N))) 0))
      (a!2 (or (= (select I G) 0) (not (= (select I G) (select I F))) (= H 1))))
  (and (not (= (select O L) 0))
       (= A (+ (- 1) N))
       (= B (+ 1 M))
       (= C (+ 1 L))
       (= D (select O M))
       (= E (select O L))
       (not a!1)
       a!2
       (= (select O L) (select O M))))
      )
      (INV_MAIN_42 F G H I E D C B A O)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and (= (select H E) (select H F))
       (not (= (select H E) 0))
       (= C 0)
       (= C G)
       (= B F)
       (= A E)
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
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and (= (select H E) (select H F))
       (not (= (select H E) 0))
       (not (= (select D A) (select D B)))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
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
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and (= (select H E) (select H F))
       (not (= (select H E) 0))
       (= (select D A) (select D B))
       (= (select D A) 0)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
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
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and (= (select H E) 0)
       (= (select D A) (select D B))
       (not (= (select D A) 0))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
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
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0))))
  (and (not (= (select H E) (select H F)))
       (not (= (select H E) 0))
       (= (select D A) (select D B))
       (not (= (select D A) 0))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
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
        (and (= (select D A) (select D B))
     (not (= (select D A) 0))
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (<= (ite (>= G 0) G (* (- 1) G)) 0)
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
        (let ((a!1 (not (<= (ite (>= G 0) G (* (- 1) G)) 0)))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select H E) 0)
       (= C 0)
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (not a!2) (not (= D H)))
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
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select H E) (select H F)))
       (not (= (select H E) 0))
       (= C 0)
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (not a!2) (not (= D H)))
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
      (a!2 (= (+ (select D A) (* (- 1) (select D B)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select H E) 0)
       (not (= (select D A) (select D B)))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (not (= D H)) (not a!2))
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
      (a!2 (= (+ (select D A) (* (- 1) (select D B)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select H E) (select H F)))
       (not (= (select H E) 0))
       (not (= (select D A) (select D B)))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (not (= D H)) (not a!2))
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
        (let ((a!1 (= (+ (select D A) (* (- 1) (select D B))) 0)))
  (and (not (= (select D A) (select D B)))
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (<= (ite (>= G 0) G (* (- 1) G)) 0)
       (or (not (= D H)) (not a!1))
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
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select H E) 0)
       (= (select D A) (select D B))
       (= (select D A) 0)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (not a!2) (not (= D H)))
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
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select H E) (select H F)))
       (not (= (select H E) 0))
       (= (select D A) (select D B))
       (= (select D A) 0)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       a!1
       (or (not a!2) (not (= D H)))
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (= (+ (select D B) (* (- 1) (select D A)))
              (+ (select J G) (* (- 1) (select J H))))))
  (and (= (select J G) 0)
       (not (= C 1))
       (not a!1)
       (or (not a!2) (not (= D J)))
       (not (= (select D B) (select D A)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (= (+ (select D B) (* (- 1) (select D A)))
              (+ (select J G) (* (- 1) (select J H))))))
  (and (not (= (select J G) (select J H)))
       (not (= (select J G) 0))
       (not (= C 1))
       (not a!1)
       (or (not a!2) (not (= D J)))
       (not (= (select D B) (select D A)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (= (+ (select D B) (* (- 1) (select D A))) (+ E (* (- 1) F)))))
  (and (not (= C 1))
       a!1
       (or (not (= D J)) (not a!2))
       (not (= (select D B) (select D A)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (= (select D B) 0)
       (= (select J G) 0)
       (not (= C 1))
       (not a!1)
       (or (not a!2) (not (= D J)))
       (= (select D B) (select D A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (= (select D B) 0)
       (not (= (select J G) (select J H)))
       (not (= (select J G) 0))
       (not (= C 1))
       (not a!1)
       (or (not a!2) (not (= D J)))
       (= (select D B) (select D A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (not (= 0 (+ E (* (- 1) F))))))
  (and (= (select D B) 0)
       (not (= C 1))
       a!1
       (or (not (= D J)) a!2)
       (= (select D B) (select D A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (= C 1) (not a!1) (or (not a!2) (not (= D J))) (= (select J G) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (not (= (select J G) 0))
       (= C 1)
       (not a!1)
       (or (not a!2) (not (= D J)))
       (not (= (select J G) (select J H)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I J)
        (let ((a!1 (<= (ite (>= I 1) (+ (- 1) I) (+ 1 (* (- 1) I))) 0))
      (a!2 (not (= 0 (+ E (* (- 1) F))))))
  (and a!1 (or (not (= D J)) a!2) (= C 1)))
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
