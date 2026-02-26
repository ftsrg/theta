(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (= A C) (= B D) (= 0 v_4) (= v_5 C))
      )
      (INV_MAIN_42 A v_4 B C v_5 D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J)
        (let ((a!1 (= C (store G (+ E (* 4 F)) 0)))
      (a!2 (= (select G (+ E (* 4 F))) 0)))
  (and a!1
       (not a!2)
       (not (= (select J I) 0))
       (= B (+ 4 I))
       (= D (+ 1 F))
       (= A (store J I 0))))
      )
      (INV_MAIN_42 E D C H B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (let ((a!1 (= (select E (+ C (* 4 D))) 0))
      (a!2 (= A (store E (+ C (* 4 D)) 0))))
  (and (not a!1) (= (select H G) 0) (= B (+ 1 D)) a!2))
      )
      (INV_MAIN_42 C B A F G H)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (let ((a!1 (= (select E (+ C (* 4 D))) 0)))
  (and a!1 (not (= (select H G) 0)) (= B (+ 4 G)) (= A (store H G 0))))
      )
      (INV_MAIN_42 C D E F B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (= B (div (+ E (* (- 1) D)) 4)))
      (a!2 (= (select C (+ A (* 4 B))) 0)))
  (and (= (select F E) 0) (or (not a!1) (not (= C F))) a!2))
      )
      false
    )
  )
)

(check-sat)
(exit)
