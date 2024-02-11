; ./extra-small-lia/./yz_plus_minus_2_000.smt2
(set-logic HORN)

(declare-fun |inv| ( Int Int Int Int ) Bool)

(assert
  (forall ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and true (= 0 v_0) (= 0 v_1) (= 0 v_2) (= 0 v_3))
      )
      (inv v_0 v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv A D B C)
        (and (= G (+ (- 1) C))
     (= F (+ 1 B))
     (= E (+ A C))
     (not (<= 10000 A))
     (= H (+ 1 D)))
      )
      (inv E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv D A B C)
        (not (>= D 0))
      )
      false
    )
  )
)

(check-sat)
(exit)
