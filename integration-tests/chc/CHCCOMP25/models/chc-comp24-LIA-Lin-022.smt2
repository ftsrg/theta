(set-logic HORN)


(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@_bb| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (main@entry B)
        (and (or (not E) (not D) (= C 1))
     (or (not E) (not D) (= F 0))
     (or (not E) (not D) (= H F))
     (or (not E) (not D) (= I C))
     (or (not D) (and E D))
     (= D true)
     (= A B))
      )
      (main@_bb G H I)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (main@_bb M C F)
        (and (or (not K) (not B) (not A))
     (or (not K) (not J) (= I G))
     (or (not K) (not J) (= L H))
     (or (not K) (not J) (= N L))
     (or (not K) (not J) (= O I))
     (or (not J) (and K J))
     (or (not K) (= D (= F 4)))
     (or (not K) (= E (+ 2 C)))
     (or (not K) (= G (+ 1 F)))
     (or (not K) (= H (ite D (- 10) E)))
     (or (not K) (and K A))
     (= J true)
     (not (= (<= F M) B)))
      )
      (main@_bb M N O)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) ) 
    (=>
      (and
        (main@_bb D F A)
        (and (or (not K) C (not B))
     (or (not K) (= H (= F 0)))
     (or (not K) (= I (or G H)))
     (or (not K) (= G (= F E)))
     (or (not K) (= E (* 2 D)))
     (or (not K) (= M (ite I 1 0)))
     (or (not K) (and K B))
     (or (not K) (not J))
     (or (not L) (and L K))
     (or (not O) (= N (= M 0)))
     (or (not O) (and O L))
     (or (not P) (and P O))
     (or (not Q) (and Q P))
     (or (not R) (and R Q))
     (or N (not O))
     (= R true)
     (not (= (<= A D) C)))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
