(set-logic HORN)


(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@_bb| ( Int Int Int ) Bool)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q Int) (R Int) ) 
    (=>
      (and
        (main@entry R D)
        (let ((a!1 (= H (and (not (<= 199 E)) (>= E 0))))
      (a!2 (= G (and (not (<= 199 F)) (>= F 0)))))
  (and a!1
       (= I (and H G))
       (= A D)
       (= B D)
       (= C D)
       (= E (+ 99 K))
       (= F (+ 99 J))
       (or (not N) (not M) (= L J))
       (or (not N) (not M) (= O K))
       (or (not N) (not M) (= P O))
       (or (not N) (not M) (= Q L))
       (or (not M) (and N M))
       (= I true)
       (= M true)
       a!2))
      )
      (main@_bb P Q R)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) ) 
    (=>
      (and
        (main@_bb H K V)
        (and (not (= (<= K 100) B))
     (= D (and B A))
     (or (not F) D (not C))
     (or (not N) (not G) (not F))
     (or (not Q) (and R Q) (and Q N))
     (or (not Q) (not N) (= M I))
     (or (not Q) (not N) (= O J))
     (or (not Q) (not N) (= T O))
     (or (not Q) (not N) (= U M))
     (or (not R) (not F) G)
     (or (not R) (not Q) (= P K))
     (or (not R) (not Q) (= S L))
     (or (not R) (not Q) (= T S))
     (or (not R) (not Q) (= U P))
     (or (not F) (= E V))
     (or (not F) (and F C))
     (or (not N) (= I (+ (- 1) K)))
     (or (not N) (= J (+ (- 1) H)))
     (or (not N) (and N F))
     (or (not R) (= L (+ 1 H)))
     (or (not R) (and R F))
     (= Q true)
     (not (= (<= 100 H) A)))
      )
      (main@_bb T U V)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) ) 
    (=>
      (and
        (main@_bb F G A)
        (let ((a!1 (or (not L) (not (= (<= 101 G) I))))
      (a!2 (or (not L) (not (= (<= F 99) H)))))
  (and (not (= (<= G 100) C))
       (= E (and C B))
       (or (not D) (not E) (not L))
       a!1
       a!2
       (or (not L) (= J (or I H)))
       (or (not L) (= N (ite J 1 0)))
       (or (not L) (and D L))
       (or (not M) (and M L))
       (or (not K) (not L))
       (or (not P) (= O (= N 0)))
       (or (not P) (and P M))
       (or (not Q) (and Q P))
       (or (not R) (and R Q))
       (or (not S) (and S R))
       (or O (not P))
       (= S true)
       (not (= (<= 100 F) B))))
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
