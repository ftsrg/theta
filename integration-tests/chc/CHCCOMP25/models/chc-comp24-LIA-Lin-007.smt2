(set-logic HORN)


(declare-fun |main@orig.main.exit.split| ( ) Bool)
(declare-fun |main@.lr.ph.split.us| ( Int Int Int ) Bool)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Int) ) 
    (=>
      (and
        (main@entry Q D)
        (and (not (= (<= I 100) F))
     (= H (and F E))
     (= A D)
     (= B D)
     (= C D)
     (or (not G) (not M) H)
     (or (not M) (not L) (= K I))
     (or (not M) (not L) (= N J))
     (or (not M) (not L) (= O K))
     (or (not M) (not L) (= P N))
     (or (not L) (and M L))
     (or (not M) (and M G))
     (= L true)
     (not (= (<= 100 J) E)))
      )
      (main@.lr.ph.split.us O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Int) (Q Int) (R Int) (S Int) ) 
    (=>
      (and
        (main@_bb C F S)
        (let ((a!1 (or (not O) (not (= (<= 101 G) H))))
      (a!2 (or (not O) (not (= (<= K 100) I)))))
  (and (or (not O) (not D) (= G E))
       (or (not O) (not D) (= E C))
       (or (not O) (not D) (not B))
       (or (not O) (not N) (= M K))
       (or (not O) (not N) (= P L))
       (or (not O) (not N) (= Q M))
       (or (not O) (not N) (= R P))
       (or (not O) (not N) J)
       (or (not N) (and O N))
       a!1
       a!2
       (or (not O) (= J (and I H)))
       (or (not O) (= K (+ (- 1) F)))
       (or (not O) (= L (+ (- 1) G)))
       (or (not O) (and O D))
       (= N true)
       (= A S)))
      )
      (main@.lr.ph.split.us Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) ) 
    (=>
      (and
        (main@entry A E)
        (and (not (= (<= G 100) I))
     (= K (and I H))
     (= B E)
     (= C E)
     (= D E)
     (or (not J) (not K) (not M))
     (or (not M) (and M J))
     (or (not M) (not L))
     (or (not N) (and N M))
     (= N true)
     (not (= (<= 100 F) H)))
      )
      main@orig.main.exit.split
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Int) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) ) 
    (=>
      (and
        (main@_bb N E B)
        (let ((a!1 (or (not P) (not (= (<= 100 O) Q))))
      (a!2 (or (not J) (not (= (<= 101 F) H))))
      (a!3 (or (not J) (not (= (<= G 100) I)))))
  (and (or (not L) (not J) (= C N))
       (or (not L) (not J) (= F C))
       (or (not L) M (not P))
       (or (not M) (not L) (not J))
       (or (not S) (not Q) (not P))
       (or (not R) (not K) (not J))
       (or (and U R) (not U) (and U S))
       a!1
       (or (not P) (= O (+ 1 N)))
       (or (not P) (and L P))
       (or (not S) (and S P))
       a!2
       a!3
       (or (not J) (= K (and I H)))
       (or (not J) (= D (+ (- 1) F)))
       (or (not J) (= G (+ (- 1) E)))
       (or (not J) (and L J))
       (or (not R) (and R J))
       (or (not U) (not T))
       (or (not V) (and V U))
       (= V true)
       (= A B)))
      )
      main@orig.main.exit.split
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (main@.lr.ph.split.us F A G)
        (and (or (not C) (not B) (= E D))
     (or (not B) (and C B))
     (= B true)
     (or (not C) (not B) (= D A)))
      )
      (main@_bb E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (main@_bb D K L)
        (let ((a!1 (or (not H) (not (= (<= 100 F) E)))))
  (and (or (not B) (not H) C)
       (or (not H) (not G) (= I F))
       (or (not H) (not G) (= J I))
       (or (not H) (not G) E)
       (or (not G) (and H G))
       a!1
       (or (not H) (= F (+ 1 D)))
       (or (not H) (and H B))
       (= G true)
       (= A L)))
      )
      (main@_bb J K L)
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
