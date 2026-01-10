(set-logic HORN)


(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (select (store K G (select K H)) H) I)))
  (and (= D (store K G (select K H)))
       (= K P)
       (not a!1)
       (not (= (select P M) N))
       (= B (+ 1 L))
       (= C (+ 1 M))
       (= E (+ 1 G))
       (= F (+ (- 1) J))
       (not (= O 0))
       (not (= J 0))
       (= J O)
       (= I N)
       (= H M)
       (= G L)
       (= A (store P L (select P M)))))
      )
      (INV_MAIN_0 H I F E D N C B O A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) (N Int) (O Int) (P Int) (Q Int) (R (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 I J K L M N O P Q R)
        (let ((a!1 (= E (store M L (select M (+ 1 I)))))
      (a!2 (select (store M L (select M (+ 1 I))) (+ 1 I))))
  (and a!1
       (not (= a!2 J))
       (not (= (select R O) N))
       (= B (+ (- 1) Q))
       (= C (+ 1 P))
       (= F (+ 1 L))
       (= D (+ 1 O))
       (= G (+ (- 1) K))
       (= H (+ 1 I))
       (not (= Q 1))
       (not (= K 0))
       (= A (store R P (select R O)))))
      )
      (INV_MAIN_0 H J G F E N D C B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 E F G H I J K L M N)
        (let ((a!1 (select (store I H (select I (+ 1 E))) (+ 1 E)))
      (a!2 (= A (store I H (select I (+ 1 E))))))
  (and (not (= a!1 F))
       (= B (+ 1 H))
       (= C (+ (- 1) G))
       (= D (+ 1 E))
       (not (= G 0))
       (or (= M 1) (= (select N K) J))
       a!2))
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
        (let ((a!1 (select (store I H (select I (+ 1 E))) (+ 1 E))))
  (and (not (= (select N K) J))
       (= B (+ (- 1) M))
       (= C (+ 1 L))
       (= D (+ 1 K))
       (not (= M 1))
       (or (= G 0) (= a!1 F))
       (= A (store N L (select N K)))))
      )
      (INV_MAIN_0 E F G H I J D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (select (store E A (select E B)) B) C)))
  (and a!1
       (not (= (select J G) H))
       (not (= I 0))
       (not (= D 0))
       (= D I)
       (= C H)
       (= B G)
       (= A F)
       (= E J)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select J G) H))
     (not (= I 0))
     (= D 0)
     (= D I)
     (= C H)
     (= B G)
     (= A F)
     (= E J))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (select (store E A (select E B)) B) C)))
  (and (not a!1)
       (= (select J G) H)
       (not (= I 0))
       (not (= D 0))
       (= D I)
       (= C H)
       (= B G)
       (= A F)
       (= E J)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (select (store E A (select E B)) B) C)))
  (and (not a!1) (= I 0) (not (= D 0)) (= D I) (= C H) (= B G) (= A F) (= E J)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (select (store E A (select E B)) B) C))
      (a!2 (not (= (store E A (select E B)) (store J F (select J G))))))
  (and a!1
       (= (select J G) H)
       (not (= I 0))
       (not (= D 0))
       (= D I)
       (= C H)
       (= B G)
       (= A F)
       (or (not (= A F)) a!2)
       (= E J)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (select (store E A (select E B)) B) C))
      (a!2 (not (= (store E A (select E B)) J))))
  (and a!1
       (= I 0)
       (not (= D 0))
       (= D I)
       (= C H)
       (= B G)
       (= A F)
       (or (not (= A (- 1))) a!2)
       (= E J)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (not (= E (store J F (select J G))))))
  (and (= (select J G) H)
       (not (= I 0))
       (= D 0)
       (= D I)
       (= C H)
       (= B G)
       (= A F)
       (or (not (= (- 1) F)) a!1)
       (= E J)))
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
        (let ((a!1 (= (store E D (select E (+ 1 A))) (store J H (select J G))))
      (a!2 (select (store E D (select E (+ 1 A))) (+ 1 A))))
  (and (= (select J G) F)
       (not (= I 1))
       (not (= C 0))
       (or (not (= D H)) (not a!1))
       (= a!2 B)))
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
        (let ((a!1 (= (store E D (select E (+ 1 A))) J))
      (a!2 (select (store E D (select E (+ 1 A))) (+ 1 A))))
  (and (= I 1) (not (= C 0)) (or (not (= D (- 1))) (not a!1)) (= a!2 B)))
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
        (let ((a!1 (not (= E (store J H (select J G))))))
  (and (not (= I 1)) (= C 0) (or (not (= (- 1) H)) a!1) (= (select J G) F)))
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
        (and (= I 1) (= C 0) (not (= E J)))
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
