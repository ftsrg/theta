(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (= E 0) (= C F) (= B 0) (= A 0) (= F (+ (- 1) D)))
      )
      (INV_MAIN_42 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 F G C H I)
        (and (= H (+ 1 D))
     (= G (+ (- 1) B))
     (= F (+ (- 1) A))
     (>= (+ (* 2 C) (* (- 1) F)) 1)
     (>= H 1)
     (= I (+ (- 2) E)))
      )
      (INV_MAIN_42 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (INV_MAIN_42 F G C D E)
        (and (= F (+ (- 1) A))
     (>= (+ (* 2 C) (* (- 1) F)) 1)
     (not (>= D 1))
     (= G (+ (- 1) B)))
      )
      (INV_MAIN_42 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C F G)
        (let ((a!1 (not (>= (+ (* 2 C) (* (- 1) A)) 1))))
  (and (= F (+ 1 D)) a!1 (>= F 1) (= G (+ (- 2) E))))
      )
      (INV_MAIN_42 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (INV_MAIN_42 E A D C B)
        (let ((a!1 (not (>= (+ (* 2 D) (* (- 1) E)) 1))))
  (and a!1 (not (>= C 1)) (not (= A B))))
      )
      false
    )
  )
)

(check-sat)
(exit)
