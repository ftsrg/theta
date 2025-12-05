(set-logic HORN)


(declare-fun |inv_main2| ( ) Bool)
(declare-fun |inv_main5| ( Int ) Bool)
(declare-fun |inv_main4| ( Int ) Bool)

(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      inv_main2
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (inv_main4 A)
        (and (not (<= A 268435454)) (<= 0 A))
      )
      (inv_main5 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv_main4 B)
        (and (<= 0 A) (<= 0 B) (<= B 268435454) (= A (+ 1 B)))
      )
      (inv_main4 A)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        inv_main2
        (<= 0 A)
      )
      (inv_main4 A)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (inv_main5 A)
        (and (<= 0 A) (not (<= 268435456 A)))
      )
      false
    )
  )
)

(check-sat)
(exit)
