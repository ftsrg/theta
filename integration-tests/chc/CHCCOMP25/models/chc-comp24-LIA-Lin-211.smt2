(set-logic HORN)


(declare-fun |inv_main2| ( ) Bool)
(declare-fun |inv_main5| ( Int Int ) Bool)
(declare-fun |inv_main6| ( Int Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv_main5 C B)
        (and (= A (+ 1 C))
     (<= 0 D)
     (<= 0 C)
     (<= 0 B)
     (<= 0 A)
     (<= C 1023)
     (= D (+ 1 B)))
      )
      (inv_main5 A D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        inv_main2
        (and (<= 0 B) (<= 0 A) (= A (+ 1 B)))
      )
      (inv_main5 B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv_main5 A B)
        (and (<= 0 A) (not (<= A 1023)) (<= 0 B))
      )
      (inv_main6 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv_main6 B A)
        (and (<= 0 B) (<= 0 A) (not (= B A)))
      )
      false
    )
  )
)

(check-sat)
(exit)
