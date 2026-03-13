(set-logic HORN)


(declare-fun |INV1| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) ) 
    (=>
      (and
        (INV1 A B C D E F G O Q P K L M N)
        (let ((a!1 (not (>= (+ A (* (- 1) C)) 1))))
  (and (= O 10)
       (= O (+ (- 1) H))
       (= L N)
       (= K M)
       (= I 10)
       (>= (+ F (* (- 1) O)) 1)
       a!1
       (= (+ P Q) J)))
      )
      (INV1 A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) ) 
    (=>
      (and
        (INV1 A B C D E F G O P Q K L M N)
        (let ((a!1 (not (>= (+ A (* (- 1) C)) 1))))
  (and (= P (+ (- 5) I))
       (not (= O 10))
       (= O (+ (- 1) H))
       (= L N)
       (= K M)
       (>= (+ F (* (- 1) O)) 1)
       a!1
       (= (+ Q P) J)))
      )
      (INV1 A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) ) 
    (=>
      (and
        (INV1 A B O T P F G Q S R K L M N)
        (and (= (+ (* 5 O) B) D)
     (= (+ R S) J)
     (= Q 10)
     (= Q (+ (- 1) H))
     (= O (+ (- 1) C))
     (= L N)
     (= K M)
     (= I 10)
     (>= (+ A (* (- 1) O)) 1)
     (>= (+ F (* (- 1) Q)) 1)
     (= (+ P (* 5 O) B) E))
      )
      (INV1 A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) ) 
    (=>
      (and
        (INV1 A B O T P F G Q R S K L M N)
        (and (= (+ (* 5 O) B) D)
     (= (+ S R) J)
     (= R (+ (- 5) I))
     (not (= Q 10))
     (= Q (+ (- 1) H))
     (= O (+ (- 1) C))
     (= L N)
     (= K M)
     (>= (+ A (* (- 1) O)) 1)
     (>= (+ F (* (- 1) Q)) 1)
     (= (+ P (* 5 O) B) E))
      )
      (INV1 A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) ) 
    (=>
      (and
        (INV1 A B O Q P F G H I J K L M N)
        (let ((a!1 (not (>= (+ F (* (- 1) H)) 1))))
  (and (= (+ (* 5 O) B) D)
       (= O (+ (- 1) C))
       (= L N)
       (= K M)
       a!1
       (>= (+ A (* (- 1) O)) 1)
       (= (+ P (* 5 O) B) E)))
      )
      (INV1 A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int) (v_13 Int) ) 
    (=>
      (and
        (and (= H 0)
     (= E 0)
     (= D 0)
     (= C 0)
     (= B G)
     (= A F)
     (= I 0)
     (= v_9 G)
     (= v_10 A)
     (= v_11 B)
     (= v_12 F)
     (= v_13 G))
      )
      (INV1 A B C D E F G H v_9 I v_10 v_11 v_12 v_13)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (INV1 C G D H A E I F J B K L M N)
        (let ((a!1 (not (>= (+ E (* (- 1) F)) 1))) (a!2 (not (>= (+ C (* (- 1) D)) 1))))
  (and (= K M) (not (= A B)) a!1 a!2 (= L N)))
      )
      false
    )
  )
)

(check-sat)
(exit)
