(set-logic HORN)


(declare-fun |inv_main17| ( Int Int Int Int Int ) Bool)
(declare-fun |inv_main8| ( Int Int Int Int ) Bool)
(declare-fun |inv_main3| ( Int ) Bool)
(declare-fun |inv_main21| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (inv_main3 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (inv_main17 C G F E D)
        (and (= B (+ 2 D)) (<= D 9) (= A (+ 4 (* 2 D))))
      )
      (inv_main17 C G F B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv_main8 C F D E)
        (and (= B (+ 4 (* 2 D))) (<= D 9) (= A (+ 2 D)))
      )
      (inv_main8 C F B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv_main17 B F E D C)
        (and (not (<= C 9)) (= A (* 2 C)))
      )
      (inv_main21 B F A)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (inv_main3 A)
        (and (= v_1 A) (= 1 v_2) (= 0 v_3))
      )
      (inv_main8 A v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (inv_main8 B E C D)
        (and (not (<= C 9)) (= A (* 2 C)) (= v_5 B) (= 0 v_6) (= 1 v_7))
      )
      (inv_main17 B A v_5 v_6 v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (inv_main21 B C A)
        (not (= C A))
      )
      false
    )
  )
)

(check-sat)
(exit)
