(set-logic HORN)


(declare-fun |fib_1030$unknown:7| ( Int Int Int ) Bool)
(declare-fun |fail$unknown:3| ( Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (|fib_1030$unknown:7| A C B)
        (let ((a!1 (= (= 0 O) (and (not (= 0 N)) (not (= 0 J))))))
  (and (not a!1)
       (not (= (= 0 N) (>= M 0)))
       (not (= 0 B))
       (= 0 O)
       (= L A)
       (= K 0)
       (= I (+ G H))
       (= H A)
       (= G 0)
       (= F (+ D E))
       (= E C)
       (= D 0)
       (= P 1)
       (= M (+ K L))
       (= (= 0 J) (<= F I))))
      )
      (|fail$unknown:3| P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (= B 0) (= C 0))
      )
      (|fib_1030$unknown:7| A C B)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (|fail$unknown:3| A)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
