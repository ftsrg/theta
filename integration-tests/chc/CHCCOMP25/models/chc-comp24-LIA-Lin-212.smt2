(set-logic HORN)


(declare-fun |inv_main5| ( Int Int ) Bool)
(declare-fun |inv_main4| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (= A 1) (= B 0))
      )
      (inv_main4 B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv_main4 A B)
        (and (<= 0 A) (not (<= A 5)) (<= 0 B))
      )
      (inv_main5 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv_main4 D B)
        (and (= A (+ 1 D)) (<= 0 B) (<= 0 D) (<= D 5) (= (+ C (* (- 2) B)) 0))
      )
      (inv_main4 A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv_main5 B A)
        (and (= C 0)
     (<= (- 2) C)
     (<= 0 B)
     (<= 0 A)
     (<= C 2)
     (or (not (<= 1 C)) (<= 1 A))
     (or (not (<= C (- 1))) (<= A (- 1)))
     (= A (+ (* 3 D) C)))
      )
      false
    )
  )
)

(check-sat)
(exit)
