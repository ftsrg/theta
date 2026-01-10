(set-logic HORN)


(declare-fun |inv_main8| ( Int Int Int Int ) Bool)
(declare-fun |inv_main3| ( Int ) Bool)
(declare-fun |inv_main25| ( Int Int Int ) Bool)
(declare-fun |inv_main19| ( Int Int Int Int Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv_main19 E D C H G)
        (and (= B (+ (- 1) H)) (not (= F 0)) (<= 0 H) (= A (+ 1 G)))
      )
      (inv_main19 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (inv_main8 E C D F)
        (and (= B (+ 1 D)) (not (= G 0)) (<= 0 (+ C (* (- 1) D))) (= A (+ 1 F)))
      )
      (inv_main8 E C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv_main19 C B A F E)
        (or (not (<= 0 F)) (= D 0))
      )
      (inv_main25 C B E)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (inv_main3 A)
        (and (= v_1 A) (= 0 v_2) (= 0 v_3))
      )
      (inv_main8 A v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (inv_main8 C A B D)
        (let ((a!1 (not (<= 0 (+ A (* (- 1) B))))))
  (and (or a!1 (= E 0)) (= v_5 C) (= v_6 C) (= 0 v_7)))
      )
      (inv_main19 C D v_5 v_6 v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (inv_main25 C B A)
        (not (= B A))
      )
      false
    )
  )
)

(check-sat)
(exit)
