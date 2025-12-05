(set-logic HORN)


(declare-fun |inv| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= C 0) (= B 1) (or (= A 0) (= A 1)) (= D A))
      )
      (inv D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv G F E H)
        (let ((a!1 (= B (ite (= H (mod G 2)) (+ E F) (+ (- 1) E)))))
  (and (= C (+ (- 3) F G)) a!1 (= A (+ 1 (* (- 1) H))) (= D (+ 1 G))))
      )
      (inv D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv B D A C)
        (and (not (<= B 10)) (>= A 0))
      )
      false
    )
  )
)

(check-sat)
(exit)
