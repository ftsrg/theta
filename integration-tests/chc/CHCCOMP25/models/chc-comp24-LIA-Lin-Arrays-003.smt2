(set-logic HORN)


(declare-fun |main@entry| ( ) Bool)
(declare-fun |main@postcall2| ( Bool (Array Int Int) Int Int Int ) Bool)
(declare-fun |main@precall3.split| ( ) Bool)

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
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E (Array Int Int)) (F Int) (G (Array Int Int)) (H Bool) (I Bool) (J Bool) (K Int) (L Bool) (M (Array Int Int)) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        main@entry
        (and (= P (+ 4 D))
     (not (<= D 0))
     (or (not J) (not (<= F 0)) (<= D 0))
     (or (not B) C (not J))
     (or (not J) (not I) (= L H))
     (or (not J) (not I) (= G E))
     (or (not J) (not I) (= M G))
     (or (not J) (not I) (= K F))
     (or (not J) (not I) (= N K))
     (or (not J) (not I) (not H))
     (or (not (<= O 0)) (<= D 0))
     (or (not (<= P 0)) (<= D 0))
     (or (not I) (and J I))
     (or (not J) (= F D))
     (or (not J) (and J B))
     (not A)
     (= I true)
     (= O (+ 28 D)))
      )
      (main@postcall2 L M N O P)
    )
  )
)
(assert
  (forall ( (A Bool) (B (Array Int Int)) (C Int) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H Bool) (I Int) (J (Array Int Int)) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P (Array Int Int)) (Q Int) (R Int) (S Int) ) 
    (=>
      (and
        (main@postcall2 A B C R S)
        (let ((a!1 (ite (>= I 0)
                (or (not (<= S I)) (not (>= S 0)))
                (and (not (<= S I)) (not (<= 0 S)))))
      (a!2 (ite (>= R 0)
                (or (not (<= I R)) (not (>= I 0)))
                (and (not (<= I R)) (not (<= 0 I))))))
  (and (not (= E H))
       (= G (store B C 1))
       (= I (+ 4 C))
       (or (not M) (not L) (= K H))
       (or (not M) (not L) (= O K))
       (or (not M) (not L) (= J G))
       (or (not M) (not L) (= P J))
       (or (not M) (not L) (= N I))
       (or (not M) (not L) (= Q N))
       (or (not M) (not L) F)
       (or (= E (= I S)) (= E a!1))
       (or (not (<= I 0)) (<= C 0))
       (or (not L) (and M L))
       (not A)
       (not D)
       (= L true)
       (= D a!2)))
      )
      (main@postcall2 O P Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) ) 
    (=>
      (and
        main@entry
        (and (= C (+ 4 B))
     (not (<= B 0))
     (or (not I) (not F) (= H G))
     (or (not I) (not F) (not E))
     (or (not I) (not G) (not F))
     (or (<= B 0) (not (<= A 0)))
     (or (not (<= C 0)) (<= B 0))
     (or (not I) (and I F))
     (or (not I) H)
     (or (not J) (and J I))
     (not D)
     (= J true)
     (= A (+ 28 B)))
      )
      main@precall3.split
    )
  )
)
(assert
  (forall ( (A Bool) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Bool) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) ) 
    (=>
      (and
        (main@postcall2 A C D E H)
        (let ((a!1 (ite (>= E 0)
                (or (not (<= G E)) (not (>= G 0)))
                (and (not (<= G E)) (not (<= 0 G)))))
      (a!2 (ite (>= G 0)
                (or (not (<= H G)) (not (>= H 0)))
                (and (not (<= H G)) (not (<= 0 H))))))
  (and (= F a!1)
       (= B (store C D 1))
       (= G (+ 4 D))
       (or (not O) (not L) (= N M))
       (or (not O) (not L) (= M K))
       (or (not O) (not L) (not J))
       (or (not R) (not O) (= P N))
       (or (not R) (not O) (= Q P))
       (or (= I (= G H)) (= I a!2))
       (or (not (<= G 0)) (<= D 0))
       (or (not O) (and O L))
       (or (not R) (and R O))
       (or (not R) Q)
       (or (not S) (and S R))
       (not A)
       (not F)
       (= S true)
       (not (= I K))))
      )
      main@precall3.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@precall3.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
