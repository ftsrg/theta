(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (and (not (= H 0)) (= G 0) (= G H) (= C D) (= A B) (= E F))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (and (= H 0) (not (= G 0)) (= G H) (= C D) (= A B) (= E F))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= D 0)
     (= E F)
     (= C 0)
     (= C D)
     (= A B)
     (or (not (= E F)) (not (= G H)))
     (= G H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (and (= A F)
     (not (= F 0))
     (not (= D 0))
     (= D F)
     (= C G)
     (= B H)
     (= E I)
     (= v_9 C)
     (= v_10 G))
      )
      (INV_MAIN_0 B C v_9 D E G A v_10 H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_0 G F C A E I B D J H)
        (let ((a!1 (or (not (= C D)) (not (= (store E F G) (store H I J))))))
  (and (= B 1) a!1 (= A 1)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) (P Int) ) 
    (=>
      (and
        (INV_MAIN_0 K J G H I O L M P N)
        (and (= A (store N O P))
     (not (= H 1))
     (= F (+ 1 J))
     (not (= L 1))
     (= E (+ (- 1) H))
     (= C (+ 1 O))
     (= B (+ (- 1) L))
     (= D (store I J K)))
      )
      (INV_MAIN_0 K F G E D C B M P A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 H G D E F I J K L M)
        (and (not (= E 1)) (= C (+ 1 G)) (= J 1) (= B (+ (- 1) E)) (= A (store F G H)))
      )
      (INV_MAIN_0 H C D B A I J K L M)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H L I J M K)
        (and (= C (+ 1 L)) (not (= I 1)) (= G 1) (= B (+ (- 1) I)) (= A (store K L M)))
      )
      (INV_MAIN_0 D E F G H C B J M A)
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
