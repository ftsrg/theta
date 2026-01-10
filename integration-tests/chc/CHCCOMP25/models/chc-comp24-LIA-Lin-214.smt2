(set-logic HORN)


(declare-fun |inv_main5| ( Int Int ) Bool)
(declare-fun |inv_main4| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (= A 0) (= B 1))
      )
      (inv_main4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv_main4 B A)
        (and (<= 0 A) (not (<= B 5)) (<= 0 B))
      )
      (inv_main5 B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv_main4 B D)
        (and (= C (+ 1 B)) (<= 0 B) (<= 0 D) (<= B 5) (= (+ A (* (- 2) D)) 0))
      )
      (inv_main4 C A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv_main5 A B)
        (and (<= 0 B) (<= 0 A) (not (= A 6)))
      )
      false
    )
  )
)

(check-sat)
(exit)
