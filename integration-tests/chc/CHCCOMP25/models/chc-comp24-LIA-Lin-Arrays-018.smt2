(set-logic HORN)


(declare-fun |main@entry| ( ) Bool)
(declare-fun |main@postcall2| ( Bool (Array Int Int) Int Int ) Bool)
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
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E (Array Int Int)) (F Int) (G (Array Int Int)) (H Bool) (I Bool) (J Bool) (K Int) (L Bool) (M (Array Int Int)) (N Int) (O Int) ) 
    (=>
      (and
        main@entry
        (and (not (<= D 0))
     (or (not J) (not (<= F 0)) (<= D 0))
     (or (not J) C (not B))
     (or (not J) (not I) (= L H))
     (or (not J) (not I) (= G E))
     (or (not J) (not I) (= M G))
     (or (not J) (not I) (= K F))
     (or (not J) (not I) (= N K))
     (or (not J) (not I) (not H))
     (or (not (<= O 0)) (<= D 0))
     (or (not I) (and J I))
     (or (not J) (= F D))
     (or (not J) (and J B))
     (not A)
     (= I true)
     (= O (+ 4 D)))
      )
      (main@postcall2 L M N O)
    )
  )
)
(assert
  (forall ( (A Bool) (B (Array Int Int)) (C Int) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H Bool) (I Int) (J (Array Int Int)) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P (Array Int Int)) (Q Int) (R Int) ) 
    (=>
      (and
        (main@postcall2 A B C R)
        (let ((a!1 (ite (>= I 0)
                (or (not (<= R I)) (not (>= R 0)))
                (and (not (<= R I)) (not (<= 0 R)))))
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
       (or (= E (= I R)) (= E a!1))
       (or (not (<= I 0)) (<= C 0))
       (or (not L) (and M L))
       (not A)
       (not D)
       (= L true)
       (= D a!2)))
      )
      (main@postcall2 O P Q R)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) ) 
    (=>
      (and
        main@entry
        (and (not (<= A 0))
     (or (not H) (not E) (= G F))
     (or (not H) (not E) (not D))
     (or (not F) (not H) (not E))
     (or (not (<= B 0)) (<= A 0))
     (or (not H) (and H E))
     (or (not H) G)
     (or (not I) (and I H))
     (not C)
     (= I true)
     (= B (+ 4 A)))
      )
      main@precall3.split
    )
  )
)
(assert
  (forall ( (A Bool) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Bool) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) ) 
    (=>
      (and
        (main@postcall2 A C D G)
        (let ((a!1 (ite (>= G 0)
                (or (not (<= F G)) (not (>= F 0)))
                (and (not (<= F G)) (not (<= 0 F)))))
      (a!2 (ite (>= F 0)
                (or (not (<= G F)) (not (>= G 0)))
                (and (not (<= G F)) (not (<= 0 G))))))
  (and (= E a!1)
       (= B (store C D 1))
       (= F (+ 4 D))
       (or (not N) (not K) (= L J))
       (or (not N) (not K) (= M L))
       (or (not N) (not K) (not I))
       (or (not Q) (not N) (= O M))
       (or (not Q) (not N) (= P O))
       (or (= H (= F G)) (= H a!2))
       (or (not (<= F 0)) (<= D 0))
       (or (not N) (and N K))
       (or (not Q) (and Q N))
       (or (not Q) P)
       (or (not R) (and R Q))
       (not A)
       (not E)
       (= R true)
       (not (= H J))))
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
