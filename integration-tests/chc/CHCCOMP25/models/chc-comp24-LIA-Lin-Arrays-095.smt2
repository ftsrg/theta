(set-logic HORN)


(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (and (= A H)
     (not (= H 0))
     (not (= D 0))
     (= D H)
     (= C G)
     (= B F)
     (= E I)
     (= v_9 B)
     (= v_10 F))
      )
      (INV_MAIN_0 C B v_9 D E F A v_10 G I)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 G H I J K L M N O P)
        (and (= D (store K H G))
     (= B (+ (- 1) M))
     (= C (+ 1 L))
     (= E (+ (- 1) J))
     (= F (+ 1 H))
     (not (= M 1))
     (not (= J 1))
     (= A (store P L O)))
      )
      (INV_MAIN_0 G F I E D C B N O A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I J K L M)
        (and (= B (+ (- 1) G)) (= C (+ 1 E)) (= J 1) (not (= G 1)) (= A (store H E D)))
      )
      (INV_MAIN_0 D C F B A I J K L M)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I J K L M)
        (and (= B (+ (- 1) J)) (= C (+ 1 I)) (not (= J 1)) (= G 1) (= A (store M I L)))
      )
      (INV_MAIN_0 D E F G H C B K L A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (not (= G 0)) (= C 0) (= C G) (= B F) (= A E) (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= G 0) (not (= C 0)) (= C G) (= B F) (= A E) (= D H))
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
     (= C 0)
     (= C G)
     (= B F)
     (= A E)
     (or (not (= A E)) (not (= D H)))
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
        (let ((a!1 (or (not (= C H)) (not (= (store E B A) (store J F I))))))
  (and (= D 1) a!1 (= G 1)))
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
