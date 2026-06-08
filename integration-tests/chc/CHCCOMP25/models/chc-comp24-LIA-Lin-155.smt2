(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and (>= B 0) (>= A 0) (= A B) (= 0 v_2) (= 0 v_3))
      )
      (INV_MAIN_42 v_2 A v_3 B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H)
        (and (= B (+ 1 G))
     (= C (+ (- 1) F))
     (= D (+ 1 E))
     (>= F 0)
     (not (<= H 0))
     (= A (+ (- 1) H)))
      )
      (INV_MAIN_42 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F)
        (and (= B (+ 1 C)) (>= D 0) (<= F 0) (= A (+ (- 1) D)))
      )
      (INV_MAIN_42 B A E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F)
        (and (= B (+ 1 E)) (not (>= D 0)) (not (<= F 0)) (= A (+ (- 1) F)))
      )
      (INV_MAIN_42 C D B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D)
        (and (not (>= B 0)) (<= D 0) (not (= A (+ 1 C))))
      )
      false
    )
  )
)

(check-sat)
(exit)
