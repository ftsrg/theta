(set-logic HORN)


(declare-fun |inv_main28| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main12| ( Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main3| ( Int Int ) Bool)
(declare-fun |inv_main38| ( Int Int Int Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) ) 
    (=>
      (and
        (inv_main28 E K G J F D C H)
        (and (= B (+ 1 D))
     (not (= I 0))
     (= D 10)
     (<= 1 (+ J (* (- 1) D)))
     (= A (+ H C))
     (= 10 v_11))
      )
      (inv_main28 E K G J F B v_11 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (inv_main28 F L H K G E D I)
        (and (= B (+ 5 D))
     (= C (+ 1 E))
     (not (= J 0))
     (not (= E 10))
     (<= 1 (+ K (* (- 1) E)))
     (= A (+ I D)))
      )
      (inv_main28 F L H K G C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (inv_main12 D J H I G F K)
        (and (= B (+ (* 5 G) I))
     (= C (+ 1 G))
     (not (= E 0))
     (<= 1 (+ H (* (- 1) G)))
     (= A (+ K (* 5 G) I)))
      )
      (inv_main12 D J H I C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) 
    (=>
      (and
        (inv_main3 A B)
        (and (= v_2 A) (= v_3 B) (= 0 v_4) (= 0 v_5) (= 0 v_6))
      )
      (inv_main12 A B v_2 v_3 v_4 v_5 v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (inv_main28 D I F H E C A G)
        (let ((a!1 (not (<= 1 (+ H (* (- 1) C))))))
  (or a!1 (= B 0)))
      )
      (inv_main38 D I F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int) ) 
    (=>
      (and
        (inv_main12 A G E F D C H)
        (let ((a!1 (not (<= 1 (+ E (* (- 1) D))))))
  (and (or a!1 (= B 0)) (= v_8 A) (= v_9 G) (= 0 v_10) (= v_11 G) (= 0 v_12)))
      )
      (inv_main28 A G H v_8 v_9 v_10 v_11 v_12)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv_main38 A D B C)
        (not (= B C))
      )
      false
    )
  )
)

(check-sat)
(exit)
