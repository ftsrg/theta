(set-logic HORN)


(declare-fun |inv_main31| ( Int Int Int Int Int ) Bool)
(declare-fun |inv_main25| ( Int Int Int Int Int ) Bool)
(declare-fun |inv_main3| ( Int ) Bool)
(declare-fun |inv_main37| ( Int Int Int ) Bool)
(declare-fun |inv_main14| ( Int Int Int Int ) Bool)
(declare-fun |inv_main8| ( Int Int Int Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) ) 
    (=>
      (and
        (inv_main25 F D C E A)
        (let ((a!1 (not (<= 0 (+ C (* (- 1) E))))))
  (and (or a!1 (= B 0)) (= 1 v_6)))
      )
      (inv_main31 F D C v_6 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv_main25 H F E G D)
        (and (= B (+ 1 G)) (not (= C 0)) (<= 0 (+ E (* (- 1) G))) (= A (* 5 D)))
      )
      (inv_main25 H F E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv_main31 H F E G C)
        (and (= B (+ 1 G)) (not (= D 0)) (<= 0 (+ E (* (- 1) G))) (= A (+ C G)))
      )
      (inv_main31 H F E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (inv_main8 E C A D)
        (let ((a!1 (not (<= 0 (+ C (* (- 1) A))))))
  (and (or a!1 (= B 0)) (= 0 v_5)))
      )
      (inv_main14 E C v_5 D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (inv_main8 G E D F)
        (and (not (= C 0)) (= B (+ 1 D)) (<= 0 (+ E (* (- 1) D))) (= A (* 5 F)))
      )
      (inv_main8 G E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (inv_main14 G E D F)
        (and (not (= C 0)) (= B (+ 1 D)) (<= 0 (+ E (* (- 1) D))) (= A (+ F D)))
      )
      (inv_main14 G E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv_main31 F D B E A)
        (let ((a!1 (not (<= 0 (+ B (* (- 1) E))))))
  (or a!1 (= C 0)))
      )
      (inv_main37 F D A)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (inv_main3 A)
        (and (= v_1 A) (= 1 v_2) (= 1 v_3))
      )
      (inv_main8 A v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (inv_main14 E C A D)
        (let ((a!1 (not (<= 0 (+ C (* (- 1) A))))))
  (and (or a!1 (= B 0)) (= v_5 E) (= 1 v_6) (= 1 v_7)))
      )
      (inv_main25 E D v_5 v_6 v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (inv_main37 C B A)
        (not (= B A))
      )
      false
    )
  )
)

(check-sat)
(exit)
