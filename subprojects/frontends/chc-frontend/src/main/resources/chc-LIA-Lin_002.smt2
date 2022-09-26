; ./extra-small-lia/./s_multipl_08_000.smt2
(set-logic HORN)

(declare-fun |SAD| ( Int Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (= A 0) (not (<= C 0)) (= B 0))
      )
      (FUN A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (FUN A B E)
        (and (= C (+ 1 A)) (not (<= E B)) (= D (+ 1 B)))
      )
      (FUN C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (FUN B A E)
        (and (= C B) (>= A E) (= D 0))
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (SAD A B E)
        (and (= C (+ 1 A)) (not (<= E B)) (= D (+ 1 B)))
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (SAD B A C)
        (and (>= A C) (not (>= B (* 2 C))))
      )
      false
    )
  )
)

(check-sat)
(exit)
