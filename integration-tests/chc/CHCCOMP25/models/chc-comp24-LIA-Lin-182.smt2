(set-logic HORN)


(declare-fun |inv_main19| ( Int Int Int Int ) Bool)
(declare-fun |inv_main3| ( Int ) Bool)
(declare-fun |inv_main7| ( Int Int Int ) Bool)
(declare-fun |inv_main24| ( Int Int Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv_main19 D E B F)
        (and (not (= C 0)) (not (= F B)) (<= F 10) (= A (+ 1 F)))
      )
      (inv_main19 D E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (inv_main7 C B E)
        (and (not (= D 0)) (not (= E B)) (<= E 10) (= A (+ 1 E)))
      )
      (inv_main7 C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (inv_main19 C D A E)
        (or (not (<= E 10)) (= E A) (= B 0))
      )
      (inv_main24 C D E)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) (v_2 Int) ) 
    (=>
      (and
        (inv_main3 A)
        (and (= v_1 A) (= 0 v_2))
      )
      (inv_main7 A v_1 v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (inv_main7 B A C)
        (and (or (not (<= C 10)) (= D 0)) (= v_4 B) (= 0 v_5))
      )
      (inv_main19 B C v_4 v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (inv_main7 B A D)
        (and (= D A) (<= D 10) (not (= C 0)) (= v_4 B) (= 0 v_5))
      )
      (inv_main19 B D v_4 v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (inv_main24 B C A)
        (not (= C A))
      )
      false
    )
  )
)

(check-sat)
(exit)
