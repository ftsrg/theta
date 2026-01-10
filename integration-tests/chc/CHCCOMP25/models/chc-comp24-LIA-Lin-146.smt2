(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= B D) (= A 0) (>= D 0) (>= B 0) (= C 0))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H)
        (and (= G (+ (- 1) C))
     (= F (+ 1 B))
     (= E (+ (- 1) A))
     (>= H 1)
     (>= F 0)
     (= H (+ 1 D)))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 E F C D)
        (and (= E (+ (- 1) A)) (>= F 0) (not (>= D 1)) (= F (+ 1 B)))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B E F)
        (and (= E (+ (- 1) C)) (not (>= B 0)) (>= F 1) (= F (+ 1 D)))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 A D B C)
        (and (not (>= D 0)) (not (>= C 1)) (not (= A (+ 1 B))))
      )
      false
    )
  )
)

(check-sat)
(exit)
