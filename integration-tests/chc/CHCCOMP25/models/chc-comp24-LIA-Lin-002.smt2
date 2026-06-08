(set-logic HORN)


(declare-fun |main@precall5.split| ( ) Bool)
(declare-fun |main@.lr.ph| ( Int Int ) Bool)
(declare-fun |main@entry| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        true
      )
      (main@entry A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (main@entry B G)
        (and (= A B)
     (= D G)
     (= E G)
     (= F G)
     (or (not H) (not K) I)
     (or (not K) (not J) (= L 1))
     (or (not K) (not J) (= M L))
     (or (not J) (and K J))
     (or (not K) (and K H))
     (not C)
     (= J true)
     (not (= (<= N 1) I)))
      )
      (main@.lr.ph M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (main@.lr.ph A H)
        (and (= C (* 2 A))
     (or (not E) (not D) (= F C))
     (or (not E) (not D) (= G F))
     (or (not E) (not D) B)
     (or (not D) (and E D))
     (= D true)
     (not (= (<= H C) B)))
      )
      (main@.lr.ph G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) ) 
    (=>
      (and
        (main@entry B G)
        (and (= A B)
     (= E G)
     (= D G)
     (= F G)
     (or (not J) (= M K) (not O))
     (or (not J) (not I) (not O))
     (or (not J) (not O) (not K))
     (or (not O) (not (= M N)))
     (or (not O) (and J O))
     (or (not O) N)
     (or (not P) (and P O))
     (or (not L) (not O))
     (not C)
     (= P true)
     (not (= (<= H 1) I)))
      )
      main@precall5.split
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Bool) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) ) 
    (=>
      (and
        (main@.lr.ph A B)
        (let ((a!1 (or (not I) (not (= (<= G 1) H)))))
  (and (= D (* 2 A))
       (or (not I) (not E) (= F D))
       (or (not I) (not E) (= G F))
       (or (not I) (not E) (not C))
       (or (not I) (not N) (= J H))
       (or (not I) (= L J) (not N))
       (or (not N) (not (= L M)))
       (or (not N) (and I N))
       (or (not N) M)
       (or (not O) (and O N))
       a!1
       (or (not I) (and I E))
       (or (not K) (not N))
       (= O true)
       (not (= (<= B D) C))))
      )
      main@precall5.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@precall5.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
