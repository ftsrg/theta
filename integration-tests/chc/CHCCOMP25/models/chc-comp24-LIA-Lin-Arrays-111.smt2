(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E D C F)
        (let ((a!1 (= B (div (+ C (* (- 1) D)) 4)))
      (a!2 (= (select E (+ A (* 4 B))) 0)))
  (and (= (select F C) 0) (or (not a!1) (not (= E F))) a!2))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (INV_MAIN_42 F G E H J I)
        (let ((a!1 (= (select E (+ F (* 4 G))) 0))
      (a!2 (= C (store E (+ F (* 4 G)) 0))))
  (and (= A (store I J 0))
       (not a!1)
       (not (= (select I J) 0))
       (= D (+ 1 G))
       (= B (+ 4 J))
       a!2))
      )
      (INV_MAIN_42 F D C H B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E C F G H)
        (let ((a!1 (= (select C (+ D (* 4 E))) 0))
      (a!2 (= A (store C (+ D (* 4 E)) 0))))
  (and (not a!1) (= (select H G) 0) (= B (+ 1 E)) a!2))
      )
      (INV_MAIN_42 D B A F G H)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F H G)
        (let ((a!1 (= (select E (+ C (* 4 D))) 0)))
  (and a!1 (not (= (select G H) 0)) (= B (+ 4 H)) (= A (store G H 0))))
      )
      (INV_MAIN_42 C D E F B A)
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
