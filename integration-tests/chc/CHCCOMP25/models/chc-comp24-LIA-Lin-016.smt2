(set-logic HORN)


(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@orig.main.exit.split| ( ) Bool)
(declare-fun |main@.lr.ph| ( Int Int Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (main@entry B)
        (and (= A B)
     (or (not G) (not D) (not C))
     (or (not G) (not F) (= E 0))
     (or (not G) (not F) (= H 1))
     (or (not G) (not F) (= J E))
     (or (not G) (not F) (= K H))
     (or (not F) (and G F))
     (or (not G) (and G C))
     (= F true)
     (not (= (<= 1 I) D)))
      )
      (main@.lr.ph I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (main@.lr.ph L A D)
        (and (= B (= D 4))
     (= C (+ 2 A))
     (= F (ite B (- 10) C))
     (= G (+ 1 D))
     (or (not J) (not I) (= H F))
     (or (not J) (not I) (= K G))
     (or (not J) (not I) (= M H))
     (or (not J) (not I) (= N K))
     (or (not J) (not I) E)
     (or (not I) (and J I))
     (= I true)
     (not (= (<= L D) E)))
      )
      (main@.lr.ph L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) ) 
    (=>
      (and
        (main@entry B)
        (and (= A B)
     (or (not N) (not D) (= H E))
     (or (not N) (not D) (= E 0))
     (or (not N) (not D) C)
     (or (not N) (= I (= H G)))
     (or (not N) (= L (or J I)))
     (or (not N) (not (= L M)))
     (or (not N) (= J (= H 0)))
     (or (not N) (= G (* 2 F)))
     (or (not N) (and N D))
     (or (not N) M)
     (or (not O) (and O N))
     (or (not K) (not N))
     (= O true)
     (not (= (<= 1 F) C)))
      )
      main@orig.main.exit.split
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Bool) (I Int) (J Int) (K Bool) (L Int) (M Int) (N Int) (O Int) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) ) 
    (=>
      (and
        (main@.lr.ph M A E)
        (and (= B (= E 4))
     (= C (+ 2 A))
     (= D (+ 1 E))
     (= G (ite B (- 10) C))
     (or (not K) (not H) (= J I))
     (or (not K) (not H) (= I G))
     (or (not K) (not H) (not F))
     (or (not U) (not K) (= O L))
     (or (not U) (not K) (= L J))
     (or (not K) (and K H))
     (or (not U) (= P (= O N)))
     (or (not U) (= S (or Q P)))
     (or (not U) (not (= S T)))
     (or (not U) (= Q (= O 0)))
     (or (not U) (= N (* 2 M)))
     (or (not U) (and U K))
     (or (not U) T)
     (or (not V) (and V U))
     (or (not R) (not U))
     (= V true)
     (not (= (<= M E) F)))
      )
      main@orig.main.exit.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@orig.main.exit.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
