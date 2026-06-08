(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_REC_g^g_PRE| ( Int (Array Int Int) Int (Array Int Int) ) Bool)
(declare-fun |INV_REC_g^g| ( Int (Array Int Int) Int (Array Int Int) Int Int (Array Int Int) (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= C E) (= A B) (= D F))
      )
      (INV_REC_g^g_PRE C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_REC_g^g G C H D E F I J)
        (let ((a!1 (or (not (= I J)) (not (= (select I G) (select J H))))))
  (and (= A B) (= G H) a!1 (= C D)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (INV_REC_g^g_PRE D C F E)
        (and (= A (store E F 1)) (= B (store C D 1)) (= 0 v_6) (= 0 v_7))
      )
      (INV_REC_g^g D C F E v_6 v_7 B A)
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
