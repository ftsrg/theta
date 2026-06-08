(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) ) 
    (=>
      (and
        (let ((a!1 (= (select (store D C (select D E)) E) F)))
  (and a!1
       (not (= (select H I) J))
       (= E I)
       (not (= G 0))
       (= F J)
       (= C A)
       (not (= B 0))
       (= B G)
       (= D H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) ) 
    (=>
      (and
        (and (not (= (select H I) J))
     (not (= G 0))
     (= F 0)
     (= F G)
     (= D J)
     (= C I)
     (= A B)
     (= E H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) ) 
    (=>
      (and
        (let ((a!1 (= (select (store D C (select D E)) E) F)))
  (and (not a!1)
       (= (select H I) J)
       (= E I)
       (not (= G 0))
       (= F J)
       (= C A)
       (not (= B 0))
       (= B G)
       (= D H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (let ((a!1 (= (select (store G F (select G H)) H) I)))
  (and (not a!1) (not (= E 0)) (= E J) (= J 0) (= I C) (= H B) (= F A) (= G D)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (let ((a!1 (= (select (store F E (select F G)) G) B))
      (a!2 (not (= (store F E (select F G)) (store I H (select I J))))))
  (and a!1
       (= (select I J) D)
       (= E H)
       (= G J)
       (not (= C 0))
       (= B D)
       (not (= A 0))
       (= A C)
       (or (not (= E H)) a!2)
       (= F I)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (select (store H G (select H I)) I) E))
      (a!2 (not (= (store H G (select H I)) J))))
  (and a!1
       (= E C)
       (= I B)
       (= G A)
       (= F 0)
       (not (= D 0))
       (= D F)
       (or (not (= G (- 1))) a!2)
       (= H J)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (let ((a!1 (not (= G (store I H (select I J))))))
  (and (= (select I J) F)
       (not (= E 0))
       (= D 0)
       (= D E)
       (= C F)
       (= B J)
       (= A H)
       (or (not (= (- 1) H)) a!1)
       (= G I)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N Int) (O (Array Int Int)) (P Int) ) 
    (=>
      (and
        (let ((a!1 (= (select (store J I (select J K)) K) G)))
  (and (= D (store J I (select J K)))
       (= A (store O N (select O P)))
       (not a!1)
       (not (= (select O P) L))
       (= C (+ 1 P))
       (= F (+ (- 1) H))
       (= K P)
       (not (= M 0))
       (= I N)
       (not (= H 0))
       (= H M)
       (= G L)
       (= E (+ 1 I))
       (= B (+ 1 N))
       (= J O)))
      )
      (INV_MAIN_0 K G F E D L C B M A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (INV_MAIN_0 G B A E F D J H C I)
        (let ((a!1 (= (store F E (select F (+ 1 G))) (store I H (select I J))))
      (a!2 (select (store F E (select F (+ 1 G))) (+ 1 G))))
  (and (= (select I J) D)
       (not (= C 1))
       (not (= A 0))
       (or (not (= E H)) (not a!1))
       (= a!2 B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 I E D G H A B C F J)
        (let ((a!1 (= (store H G (select H (+ 1 I))) J))
      (a!2 (select (store H G (select H (+ 1 I))) (+ 1 I))))
  (and (= F 1) (not (= D 0)) (or (not (= G (- 1))) (not a!1)) (= a!2 E)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B D C G F J H E I)
        (let ((a!1 (not (= G (store I H (select I J))))))
  (and (not (= E 1)) (= D 0) (or (not (= (- 1) H)) a!1) (= (select I J) F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B G C I D E F H J)
        (and (= H 1) (= G 0) (not (= I J)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) (O Int) (P Int) (Q (Array Int Int)) (R Int) ) 
    (=>
      (and
        (INV_MAIN_0 M I J K L N R P O Q)
        (let ((a!1 (= E (store L K (select L (+ 1 M)))))
      (a!2 (select (store L K (select L (+ 1 M))) (+ 1 M))))
  (and a!1
       (not (= a!2 I))
       (not (= (select Q R) N))
       (= B (+ (- 1) O))
       (= H (+ 1 M))
       (not (= O 1))
       (not (= J 0))
       (= G (+ (- 1) J))
       (= D (+ 1 R))
       (= F (+ 1 K))
       (= C (+ 1 P))
       (= A (store Q P (select Q R)))))
      )
      (INV_MAIN_0 H I G F E N D C B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 I E F G H J K L M N)
        (let ((a!1 (select (store H G (select H (+ 1 I))) (+ 1 I)))
      (a!2 (= A (store H G (select H (+ 1 I))))))
  (and (not (= a!1 E))
       (= D (+ 1 I))
       (not (= F 0))
       (= C (+ (- 1) F))
       (= B (+ 1 G))
       (or (= M 1) (= (select N K) J))
       a!2))
      )
      (INV_MAIN_0 D E C B A J K L M N)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) ) 
    (=>
      (and
        (INV_MAIN_0 E F G H I J N L K M)
        (let ((a!1 (select (store I H (select I (+ 1 E))) (+ 1 E))))
  (and (not (= (select M N) J))
       (= D (+ 1 N))
       (not (= K 1))
       (= C (+ 1 L))
       (= B (+ (- 1) K))
       (or (= G 0) (= a!1 F))
       (= A (store M L (select M N)))))
      )
      (INV_MAIN_0 E F G H I J D C B A)
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
