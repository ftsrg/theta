(set-logic HORN)


(declare-fun |inv_main15| ( Int Int Int Int Int ) Bool)
(declare-fun |inv_main33| ( Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main39| ( Int Int Int Int ) Bool)
(declare-fun |inv_main3| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        true
      )
      (inv_main3 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv_main33 F D H E G C)
        (and (= B (+ 1 E)) (<= 1 (+ C (* (- 1) E))) (= A (+ 1 G)))
      )
      (inv_main33 F D H B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv_main33 F D H E G C)
        (let ((a!1 (not (<= 1 (+ C (* (- 1) E))))))
  (and (= B (+ (- 1) G)) a!1 (<= 1 (+ E (* (- 1) C))) (= A (+ 1 C))))
      )
      (inv_main33 F D H E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (inv_main15 G E D C F)
        (and (= B (+ 1 D)) (<= 1 (+ F (* (- 1) D))) (= A (+ 1 C)))
      )
      (inv_main15 G E B A F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (inv_main15 G E D C F)
        (let ((a!1 (not (<= 1 (+ F (* (- 1) D))))))
  (and (= B (+ (- 1) C)) (<= 1 (+ D (* (- 1) F))) a!1 (= A (+ 1 F))))
      )
      (inv_main15 G E D B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Int) (v_4 Int) ) 
    (=>
      (and
        (inv_main3 C B)
        (and (<= 1 C) (= A (+ (- 1) B)) (= v_3 C) (= 1 v_4))
      )
      (inv_main15 C B v_3 A v_4)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (inv_main33 D B F C E A)
        (let ((a!1 (not (<= 1 (+ C (* (- 1) A))))) (a!2 (not (<= 1 (+ A (* (- 1) C))))))
  (and a!1 a!2))
      )
      (inv_main39 D B F E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (inv_main15 F D C B E)
        (let ((a!1 (not (<= 1 (+ C (* (- 1) E))))) (a!2 (not (<= 1 (+ E (* (- 1) C))))))
  (and a!1 a!2 (<= 1 F) (= A (+ (- 1) D)) (= v_6 F) (= 1 v_7)))
      )
      (inv_main33 F D B v_6 A v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (inv_main15 E C B A D)
        (let ((a!1 (not (<= 1 (+ D (* (- 1) B))))) (a!2 (not (<= 1 (+ B (* (- 1) D))))))
  (and a!1 (not (<= 1 E)) a!2 (= v_5 C)))
      )
      (inv_main39 E C A v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (inv_main3 B A)
        (and (not (<= 1 B)) (= v_2 A) (= v_3 A))
      )
      (inv_main39 B A v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv_main39 C B D A)
        (not (= D A))
      )
      false
    )
  )
)

(check-sat)
(exit)
