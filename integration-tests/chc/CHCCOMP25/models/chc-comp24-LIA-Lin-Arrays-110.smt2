(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= E 0) E (* (- 1) E)) 0))))
  (and (= (select G F) (select G H))
       (not (= (select G F) 0))
       (= D 0)
       (= D E)
       (= B H)
       (= A F)
       a!1
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= E 0) E (* (- 1) E)) 0))))
  (and (not (= (select C B) (select C D)))
       (= (select G F) (select G H))
       (not (= (select G F) 0))
       (= D H)
       (= B F)
       (not (= A 0))
       (= A E)
       a!1
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= E 0) E (* (- 1) E)) 0))))
  (and (= (select C D) (select C B))
       (= (select C D) 0)
       (= (select G F) (select G H))
       (not (= (select G F) 0))
       (= D F)
       (= B H)
       (not (= A 0))
       (= A E)
       a!1
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= F 0) F (* (- 1) F)) 0))))
  (and (= (select G H) 0)
       (= (select D E) (select D C))
       (not (= (select D E) 0))
       (= E H)
       (= C A)
       (not (= B 0))
       (= B F)
       a!1
       (= D G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= E 0) E (* (- 1) E)) 0))))
  (and (= (select C D) (select C B))
       (not (= (select C D) 0))
       (not (= (select G F) (select G H)))
       (not (= (select G F) 0))
       (= D F)
       (= B H)
       (not (= A 0))
       (= A E)
       a!1
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (and (= (select F G) (select F E))
     (not (= (select F G) 0))
     (not (= D 0))
     (= D H)
     (= G A)
     (= E B)
     (<= (ite (>= H 0) H (* (- 1) H)) 0)
     (= F C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) 0)))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select H E) 0)
       (= C 0)
       (= C D)
       (= B F)
       (= A E)
       a!1
       (or (not a!2) (not (= G H)))
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
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) 0)))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select H E) (select H F)))
       (not (= (select H E) 0))
       (= C 0)
       (= C D)
       (= B F)
       (= A E)
       a!1
       (or (not a!2) (not (= G H)))
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
        (let ((a!1 (not (<= (ite (>= B 0) B (* (- 1) B)) 0)))
      (a!2 (= (+ (select G C) (* (- 1) (select G D)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select G C) (select G D)))
       (= (select H E) 0)
       (= D F)
       (= C E)
       (not (= A 0))
       (= A B)
       a!1
       (or (not (= G H)) (not a!2))
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
        (let ((a!1 (not (<= (ite (>= B 0) B (* (- 1) B)) 0)))
      (a!2 (= (+ (select G C) (* (- 1) (select G D)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select G C) (select G D)))
       (not (= (select H E) (select H F)))
       (not (= (select H E) 0))
       (= D F)
       (= C E)
       (not (= A 0))
       (= A B)
       a!1
       (or (not (= G H)) (not a!2))
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
        (let ((a!1 (= (+ (select G E) (* (- 1) (select G F))) 0)))
  (and (not (= (select G E) (select G F)))
       (= F B)
       (= E A)
       (not (= C 0))
       (= C D)
       (<= (ite (>= D 0) D (* (- 1) D)) 0)
       (or (not (= G H)) (not a!1))
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
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) 0)))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select G C) (select G B))
       (= (select G C) 0)
       (= (select H E) 0)
       (= C E)
       (= B F)
       (not (= A 0))
       (= A D)
       a!1
       (or (not a!2) (not (= G H)))
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
        (let ((a!1 (not (<= (ite (>= D 0) D (* (- 1) D)) 0)))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select G C) (select G B))
       (= (select G C) 0)
       (not (= (select H E) (select H F)))
       (not (= (select H E) 0))
       (= C E)
       (= B F)
       (not (= A 0))
       (= A D)
       a!1
       (or (not a!2) (not (= G H)))
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (<= (ite (>= M 0) M (* (- 1) M)) 0))))
  (and (= (select N K) (select N L))
       (not (= (select N K) 0))
       (= (select J H) (select J G))
       (not (= (select J H) 0))
       (= E (+ 1 H))
       (= F (+ 1 G))
       (= D (select N K))
       (not (= I 0))
       (= I M)
       (= H K)
       (= G L)
       (= C (select N L))
       (= B (+ 1 K))
       (= A (+ 1 L))
       a!1
       (= J N)))
      )
      (INV_MAIN_42 F E I J D C B A M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F E C I A B G H D J)
        (let ((a!1 (<= (ite (>= D 1) (+ (- 1) D) (+ 1 (* (- 1) D))) 0))
      (a!2 (= (+ (select I E) (* (- 1) (select I F)))
              (+ (select J G) (* (- 1) (select J H))))))
  (and (= (select J G) 0)
       (not (= C 1))
       (not a!1)
       (or (not (= I J)) (not a!2))
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
        (INV_MAIN_42 F E C I A B G H D J)
        (let ((a!1 (<= (ite (>= D 1) (+ (- 1) D) (+ 1 (* (- 1) D))) 0))
      (a!2 (= (+ (select I E) (* (- 1) (select I F)))
              (+ (select J G) (* (- 1) (select J H))))))
  (and (not (= (select J G) (select J H)))
       (not (= (select J G) 0))
       (not (= C 1))
       (not a!1)
       (or (not (= I J)) (not a!2))
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
        (INV_MAIN_42 F E C I G H A B D J)
        (let ((a!1 (<= (ite (>= D 1) (+ (- 1) D) (+ 1 (* (- 1) D))) 0))
      (a!2 (= (+ (select I E) (* (- 1) (select I F))) (+ G (* (- 1) H)))))
  (and (not (= C 1))
       a!1
       (or (not (= I J)) (not a!2))
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
        (INV_MAIN_42 D E C I A B G H F J)
        (let ((a!1 (<= (ite (>= F 1) (+ (- 1) F) (+ 1 (* (- 1) F))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (= (select I E) 0)
       (= (select J G) 0)
       (not (= C 1))
       (not a!1)
       (or (not a!2) (not (= I J)))
       (= (select I E) (select I D))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E C I A B G H F J)
        (let ((a!1 (<= (ite (>= F 1) (+ (- 1) F) (+ 1 (* (- 1) F))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (= (select I E) 0)
       (not (= (select J G) (select J H)))
       (not (= (select J G) 0))
       (not (= C 1))
       (not a!1)
       (or (not a!2) (not (= I J)))
       (= (select I E) (select I D))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E C I G H A B F J)
        (let ((a!1 (<= (ite (>= F 1) (+ (- 1) F) (+ 1 (* (- 1) F))) 0))
      (a!2 (not (= 0 (+ G (* (- 1) H))))))
  (and (= (select I E) 0)
       (not (= C 1))
       a!1
       (or (not (= I J)) a!2)
       (= (select I E) (select I D))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E I C D G H F J)
        (let ((a!1 (<= (ite (>= F 1) (+ (- 1) F) (+ 1 (* (- 1) F))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (= E 1) (not a!1) (or (not a!2) (not (= I J))) (= (select J G) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E I C D G H F J)
        (let ((a!1 (<= (ite (>= F 1) (+ (- 1) F) (+ 1 (* (- 1) F))) 0))
      (a!2 (= 0 (+ (select J G) (* (- 1) (select J H))))))
  (and (not (= (select J G) 0))
       (= E 1)
       (not a!1)
       (or (not a!2) (not (= I J)))
       (not (= (select J G) (select J H)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E I G H C D F J)
        (let ((a!1 (<= (ite (>= F 1) (+ (- 1) F) (+ 1 (* (- 1) F))) 0))
      (a!2 (not (= 0 (+ G (* (- 1) H))))))
  (and a!1 (or (not (= I J)) a!2) (= E 1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) (P Int) (Q Int) (R (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 K L M N I J O P Q R)
        (let ((a!1 (<= (ite (>= Q 1) (+ (- 1) Q) (+ 1 (* (- 1) Q))) 0)))
  (and (not (= (select R O) 0))
       (= (select N L) (select N K))
       (not (= (select N L) 0))
       (= A (+ (- 1) Q))
       (= B (+ 1 P))
       (= H (+ 1 K))
       (not (= M 1))
       (= G (+ 1 L))
       (= F (+ (- 1) M))
       (= E (select R O))
       (= D (select R P))
       (= C (+ 1 O))
       (not a!1)
       (= (select R O) (select R P))))
      )
      (INV_MAIN_42 H G F N E D C B A R)
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
       (= C (+ 1 D))
       (not (= F 1))
       (= B (+ 1 E))
       (= A (+ (- 1) F))
       a!2
       (= (select G E) (select G D)))))
      )
      (INV_MAIN_42 C B A G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) (N Int) (O (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 H I J K F G L M N O)
        (let ((a!1 (<= (ite (>= N 1) (+ (- 1) N) (+ 1 (* (- 1) N))) 0))
      (a!2 (or (= (select K I) 0) (not (= (select K I) (select K H))) (= J 1))))
  (and (not (= (select O L) 0))
       (= E (select O L))
       (= D (select O M))
       (= C (+ 1 L))
       (= B (+ 1 M))
       (= A (+ (- 1) N))
       (not a!1)
       a!2
       (= (select O L) (select O M))))
      )
      (INV_MAIN_42 H I J K E D C B A O)
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
