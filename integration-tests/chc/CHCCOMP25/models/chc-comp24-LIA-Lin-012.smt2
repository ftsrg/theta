(set-logic HORN)


(declare-fun |main@.lr.ph.split.us| ( Int Int Int ) Bool)
(declare-fun |main@_bb| ( Int Int Int ) Bool)
(declare-fun |main@precall.split| ( ) Bool)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) ) 
    (=>
      (and
        (main@entry V D)
        (let ((a!1 (= G (and (not (<= 199 E)) (>= E 0))))
      (a!2 (= H (and (not (<= 199 F)) (>= F 0)))))
  (and (not (= (<= O 100) J))
       a!1
       a!2
       (= I (and H G))
       (= M (and K J))
       (= A D)
       (= B D)
       (= C D)
       (= E (+ 99 N))
       (= F (+ 99 O))
       (or (not L) M (not R))
       (or (not R) (not Q) (= P N))
       (or (not R) (not Q) (= S O))
       (or (not R) (not Q) (= T S))
       (or (not R) (not Q) (= U P))
       (or (not Q) (and R Q))
       (or (not R) (and R L))
       (= I true)
       (= Q true)
       (not (= (<= 100 N) K))))
      )
      (main@.lr.ph.split.us T U V)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Int) (Q Int) (R Int) (S Int) ) 
    (=>
      (and
        (main@_bb C F S)
        (let ((a!1 (or (not O) (not (= (<= 101 G) I))))
      (a!2 (or (not O) (not (= (<= L 100) H)))))
  (and (or (not O) (not D) (= E C))
       (or (not O) (not D) (= G E))
       (or (not O) (not D) (not B))
       (or (not O) (not N) (= M K))
       (or (not O) (not N) (= P L))
       (or (not O) (not N) (= Q P))
       (or (not O) (not N) (= R M))
       (or (not O) (not N) J)
       (or (not N) (and O N))
       a!1
       a!2
       (or (not O) (= J (and I H)))
       (or (not O) (= K (+ (- 1) G)))
       (or (not O) (= L (+ (- 1) F)))
       (or (not O) (and O D))
       (= N true)
       (= A S)))
      )
      (main@.lr.ph.split.us Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Bool) (R Int) (S Int) (T Int) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) ) 
    (=>
      (and
        (main@entry A E)
        (let ((a!1 (= H (and (not (<= 199 F)) (>= F 0))))
      (a!2 (= I (and (not (<= 199 G)) (>= G 0))))
      (a!3 (or (not Z) (not (= (<= 101 T) U))))
      (a!4 (or (not Z) (not (= (<= S 99) V)))))
  (and (not (= (<= N 100) K))
       a!1
       a!2
       (= J (and I H))
       (= M (and L K))
       (= B E)
       (= C E)
       (= D E)
       (= F (+ 99 O))
       (= G (+ 99 N))
       (or (not Q) (= P N) (not Z))
       (or (not Q) (= R O) (not Z))
       (or (not Q) (= S R) (not Z))
       (or (not Q) (= T P) (not Z))
       (or (not Q) (not M) (not Z))
       a!3
       a!4
       (or (not Z) (= X (or V U)))
       (or (not Z) (not (= X Y)))
       (or (not Z) (and Q Z))
       (or (not Z) Y)
       (or (not A1) (and A1 Z))
       (or (not W) (not Z))
       (= J true)
       (= A1 true)
       (not (= (<= 100 O) L))))
      )
      main@precall.split
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Bool) (L Int) (M Bool) (N Bool) (O Int) (P Bool) (Q Int) (R Int) (S Int) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Int) (C1 Int) (D1 Bool) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) ) 
    (=>
      (and
        (main@_bb O Q B)
        (let ((a!1 (or (not K) (not (= (<= 101 D) F))))
      (a!2 (or (not K) (not (= (<= H 100) E))))
      (a!3 (or (not T) (not (= (<= 100 R) P))))
      (a!4 (or (not M1) (not (= (<= 101 G1) H1))))
      (a!5 (or (not M1) (not (= (<= F1 99) I1)))))
  (and (or (not M) (not K) (= C O))
       (or (not M) (not K) (= D C))
       (or (not N) (not M) (not K))
       (or N (not T) (not M))
       (or (not M1) (and D1 M1) (and A1 M1))
       (or (not A1) (not K) (= J H))
       (or (not A1) (not K) (= L I))
       (or (not A1) (not K) (= V J))
       (or (not A1) (not K) (= W L))
       (or (not A1) (not K) (not G))
       (or (not M1) (= Z V) (not A1))
       (or (not M1) (= B1 W) (not A1))
       (or (not M1) (= F1 B1) (not A1))
       (or (not M1) (= G1 Z) (not A1))
       (or (not D1) (not T) (= Y U))
       (or (not D1) (not T) (= S Q))
       (or (not D1) (not T) (= U R))
       (or (not D1) (not T) (= X S))
       (or (not D1) (not T) (not P))
       (or (not D1) (not M1) (= C1 X))
       (or (not D1) (not M1) (= E1 Y))
       (or (not D1) (= F1 E1) (not M1))
       (or (not D1) (= G1 C1) (not M1))
       a!1
       a!2
       (or (not K) (= G (and F E)))
       (or (not K) (= H (+ (- 1) Q)))
       (or (not K) (= I (+ (- 1) D)))
       (or (not K) (and M K))
       a!3
       (or (not T) (= R (+ 1 O)))
       (or (not T) (and T M))
       a!4
       a!5
       (or (not M1) (= K1 (or I1 H1)))
       (or (not M1) (not (= K1 L1)))
       (or (not M1) L1)
       (or (not N1) (and N1 M1))
       (or (not A1) (and A1 K))
       (or (not D1) (and D1 T))
       (or (not J1) (not M1))
       (= N1 true)
       (= A B)))
      )
      main@precall.split
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
  (and (or (not B) C (not H))
       (or (not H) (not G) (= I F))
       (or (not H) (not G) (= J I))
       (or (not G) E (not H))
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
        main@precall.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
