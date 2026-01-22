(set-logic HORN)


(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@_bb| ( Int Int Int (Array Int Int) Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@_bb1| ( Int (Array Int Int) Int Int Int Int ) Bool)

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
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) ) 
    (=>
      (and
        (main@entry J)
        (and (not (<= I 0))
     (or (not G) (not F) (= D B))
     (or (not G) (not F) (= L D))
     (or (not G) (not F) (= E 0))
     (or (not G) (not F) (= H C))
     (or (not G) (not F) (= K E))
     (or (not G) (not F) (= M H))
     (or (not F) (and G F))
     (= F true)
     (= A J))
      )
      (main@_bb I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) (Q Int) ) 
    (=>
      (and
        (main@_bb1 A E G M N D)
        (and (or (not K) (not C) (not B))
     (or (not K) (not J) (= H E))
     (or (not K) (not J) (= P H))
     (or (not K) (not J) (= I F))
     (or (not K) (not J) (= L G))
     (or (not K) (not J) (= O I))
     (or (not K) (not J) (= Q L))
     (or (not J) (and K J))
     (or (not K) (= F (+ 1 D)))
     (or (not K) (and K B))
     (= J true)
     (= C (= A 0)))
      )
      (main@_bb M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) ) 
    (=>
      (and
        (main@_bb F A B E H)
        (and (or (not K) (not D) (not C))
     (or (not O) (= N (= M 0)))
     (or (not O) (and L O))
     (or (not O) N)
     (or (not P) (and P O))
     (or (not Q) (and Q P))
     (or (not R) (and R Q))
     (or (not K) (= I (<= G H)))
     (or (not K) (= G (select E F)))
     (or (not K) (= M (ite I 1 0)))
     (or (not K) (and K C))
     (or (not K) (not J))
     (or (not L) (and L K))
     (= R true)
     (= D (= B 0)))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (A Bool) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (main@_bb L M N B C)
        (and (or (not G) (not F) (= D B))
     (or (not G) (not F) (= J D))
     (or (not G) (not F) (= E 0))
     (or (not G) (not F) (= H C))
     (or (not G) (not F) (= I E))
     (or (not G) (not F) (= K H))
     (or (not G) (not F) A)
     (or (not F) (and G F))
     (= F true)
     (= A (= N 0)))
      )
      (main@_bb1 I J K L M N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Int) (O Bool) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U (Array Int Int)) (V Int) (W Int) (X (Array Int Int)) (Y Int) (Z Bool) (A1 Bool) (B1 Int) (C1 Int) (D1 (Array Int Int)) (E1 Int) (F1 Int) (G1 Int) (H1 Int) ) 
    (=>
      (and
        (main@_bb1 T D N F1 G1 H1)
        (let ((a!1 (or (not O) (= K (+ F1 (* 4 J)))))
      (a!2 (or (not Q) (not (= (<= N I) M))))
      (a!3 (or (not Q) (= E (+ F1 (* 4 J)))))
      (a!4 (or (not Q) (= H (+ F1 (* 4 G))))))
  (and (or (not O) (not (<= K 0)) (<= F1 0))
       (or (not Q) (<= F1 0) (not (<= E 0)))
       (or (not Q) (not (<= H 0)) (<= F1 0))
       (or (not Q) B (not A))
       (or (not Q) (not O) (not M))
       (or (not R) (not Q) (= S N))
       (or (not R) (not Q) (= W S))
       (or (not R) (not Q) M)
       (or (not A1) (and A1 O) (and R Q))
       (or (not A1) (not O) (= P L))
       (or (not A1) (not O) (= W P))
       (or (not A1) (not Z) (= X U))
       (or (not A1) (not Z) (= D1 X))
       (or (not A1) (not Z) (= Y V))
       (or (not A1) (not Z) (= B1 W))
       (or (not A1) (not Z) (= C1 Y))
       (or (not A1) (not Z) (= E1 B1))
       a!1
       (or (not O) (= L (select U K)))
       (or (not O) (not (<= F1 0)))
       (or (not O) (and Q O))
       a!2
       (or (not Q) (= U (store D E F)))
       (or (not Q) (= C G1))
       a!3
       (or (not Q) (= G (+ H1 T)))
       a!4
       (or (not Q) (= I (select U H)))
       (or (not Q) (= J (+ H1 T)))
       (or (not Q) (not (<= F1 0)))
       (or (not Q) (and Q A))
       (or (not R) Q)
       (or (not Z) (and A1 Z))
       (or (not A1) (= V (+ 1 T)))
       (= Z true)
       (= B (= T 0))))
      )
      (main@_bb1 C1 D1 E1 F1 G1 H1)
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
