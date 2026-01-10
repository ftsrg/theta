(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F) (= 0 v_6) (= 0 v_7))
      )
      (INV_MAIN_42 A v_6 B C D v_7 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A E C G B F D H)
        (and (<= C E) (or (not (= G H)) (not (= E F))) (<= D F))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) ) 
    (=>
      (and
        (INV_MAIN_42 G H E F L J I K)
        (let ((a!1 (= A (store K (+ 4 L (* 4 J)) (select K L))))
      (a!2 (store F (+ 4 G (* 4 H)) (select F (+ G (* 4 H))))))
  (and a!1 (= D (+ 1 H)) (= B (+ 1 J)) (not (<= E H)) (not (<= I J)) (= C a!2)))
      )
      (INV_MAIN_42 G D E C L B I A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F C D G H I J)
        (let ((a!1 (store D (+ 4 E (* 4 F)) (select D (+ E (* 4 F))))))
  (and (= B (+ 1 F)) (not (<= C F)) (<= I H) (= A a!1)))
      )
      (INV_MAIN_42 E B C A G H I J)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F J H G I)
        (let ((a!1 (= A (store I (+ 4 J (* 4 H)) (select I J)))))
  (and (= B (+ 1 H)) (not (<= G H)) (<= E D) a!1))
      )
      (INV_MAIN_42 C D E F J B G A)
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
