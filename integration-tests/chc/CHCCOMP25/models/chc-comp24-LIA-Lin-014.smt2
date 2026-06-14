(set-logic HORN)


(declare-fun |main@entry| ( ) Bool)
(declare-fun |main@addition.exit.split| ( ) Bool)
(declare-fun |main@.lr.ph.i| ( Int Int Int Int ) Bool)

(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      main@entry
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        main@entry
        (and (or (not E) (not B) (not A))
     (or (not E) (not D) (= C H))
     (or (not E) (not D) (= F G))
     (or (not E) (not D) (= I C))
     (or (not E) (not D) (= J F))
     (or (not D) (and E D))
     (or (not E) (and E A))
     (= D true)
     (= B (= H 0)))
      )
      (main@.lr.ph.i G H I J)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Int) (L Int) (M Bool) (N Int) (O Bool) (P Int) (Q Int) (R Int) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) ) 
    (=>
      (and
        (main@.lr.ph.i V W D C)
        (and (or (not J) (not B) (not A))
     (or (not M) (not A) B)
     (or (not T) (and T M) (and T J))
     (or (not T) (not J) (= I E))
     (or (not T) (not J) (= K F))
     (or (not T) (not J) (= P K))
     (or (not T) (not J) (= Q I))
     (or (not T) (not M) (= L G))
     (or (not T) (not M) (= N H))
     (or (not T) (not M) (= P N))
     (or (not T) (not M) (= Q L))
     (or (not T) (not S) (= R P))
     (or (not T) (not S) (= U Q))
     (or (not T) (not S) (= X R))
     (or (not T) (not S) (= Y U))
     (or (not T) (not S) (not O))
     (or (not J) (= E (+ (- 1) C)))
     (or (not J) (= F (+ 1 D)))
     (or (not J) (and J A))
     (or (not M) (= G (+ 1 C)))
     (or (not M) (= H (+ (- 1) D)))
     (or (not M) (and M A))
     (or (not S) (and T S))
     (or (not T) (= O (= P 0)))
     (= S true)
     (not (= (<= D 0) B)))
      )
      (main@.lr.ph.i V W X Y)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) ) 
    (=>
      (and
        main@entry
        (let ((a!1 (or (not I) (= G (+ D (* (- 1) E))))))
  (and (or (not B) (= C D) (not I))
       (or (not B) (= F C) (not I))
       (or (not B) A (not I))
       (or (not I) (= H (= F G)))
       a!1
       (or (not I) (and B I))
       (or (not I) (not H))
       (or (not J) (and J I))
       (= J true)
       (= A (= E 0))))
      )
      main@addition.exit.split
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Int) (L Int) (M Bool) (N Int) (O Int) (P Bool) (Q Int) (R Bool) (S Int) (T Int) (U Bool) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (C1 Bool) ) 
    (=>
      (and
        (main@.lr.ph.i W X D C)
        (let ((a!1 (or (not B1) (= Z (+ W (* (- 1) X))))))
  (and (or (not J) (not B) (not A))
       (or B (not M) (not A))
       (or (not R) (and R M) (and R J))
       (or (not R) (not J) (= Q I))
       (or (not R) (not J) (= I E))
       (or (not R) (not J) (= K F))
       (or (not R) (not J) (= O K))
       (or (not R) (not M) (= N H))
       (or (not R) (not M) (= Q L))
       (or (not R) (not M) (= L G))
       (or (not R) (not M) (= O N))
       (or (not U) (not R) (= S Q))
       (or (not U) (not R) (= T S))
       (or (not U) (not R) P)
       (or (not U) (= V T) (not B1))
       (or (not U) (= Y V) (not B1))
       (or (not J) (= E (+ (- 1) C)))
       (or (not J) (= F (+ 1 D)))
       (or (not J) (and J A))
       (or (not M) (= G (+ 1 C)))
       (or (not M) (= H (+ (- 1) D)))
       (or (not M) (and M A))
       (or (not R) (= P (= O 0)))
       (or (not B1) (= A1 (= Y Z)))
       a!1
       (or (not B1) (and U B1))
       (or (not B1) (not A1))
       (or (not C1) (and C1 B1))
       (or (not U) (and U R))
       (= C1 true)
       (not (= (<= D 0) B))))
      )
      main@addition.exit.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@addition.exit.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
