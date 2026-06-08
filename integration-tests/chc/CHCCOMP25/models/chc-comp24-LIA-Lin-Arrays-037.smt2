(set-logic HORN)


(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@_bb| ( Int (Array Int Int) Int Int Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)

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
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (main@entry M)
        (and (not (<= L 0))
     (or (not G) (not F) (= D B))
     (or (not G) (not F) (= J D))
     (or (not G) (not F) (= E 0))
     (or (not G) (not F) (= H C))
     (or (not G) (not F) (= I E))
     (or (not G) (not F) (= K H))
     (or (not F) (and G F))
     (= F true)
     (= A M))
      )
      (main@_bb I J K L M)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Int) (K Bool) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q (Array Int Int)) (R Int) (S Int) (T (Array Int Int)) (U Int) (V Bool) (W Bool) (X Int) (Y Int) (Z (Array Int Int)) (A1 Int) (B1 Int) (C1 Int) ) 
    (=>
      (and
        (main@_bb P D J B1 C1)
        (let ((a!1 (or (not K) (= G (+ B1 (* 4 P)))))
      (a!2 (or (not M) (not (= (<= F J) I))))
      (a!3 (or (not M) (= E (+ B1 (* 4 P))))))
  (and (or (not K) (not (<= G 0)) (<= B1 0))
       (or (not M) (not (<= E 0)) (<= B1 0))
       (or (not M) B (not A))
       (or (not M) (not K) (not I))
       (or (not N) (not M) (= O J))
       (or (not N) (not M) (= S O))
       (or (not N) (not M) I)
       (or (not W) (and W K) (and N M))
       (or (not W) (not K) (= L H))
       (or (not W) (not K) (= S L))
       (or (not W) (not V) (= T Q))
       (or (not W) (not V) (= Z T))
       (or (not W) (not V) (= U R))
       (or (not W) (not V) (= X S))
       (or (not W) (not V) (= Y U))
       (or (not W) (not V) (= A1 X))
       a!1
       (or (not K) (= H (select Q G)))
       (or (not K) (not (<= B1 0)))
       (or (not K) (and M K))
       a!2
       (or (not M) (= Q (store D E F)))
       (or (not M) (= C C1))
       a!3
       (or (not M) (not (<= B1 0)))
       (or (not M) (and M A))
       (or (not N) M)
       (or (not V) (and W V))
       (or (not W) (= R (+ 1 P)))
       (= V true)
       (= B (= P 0))))
      )
      (main@_bb Y Z A1 B1 C1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) ) 
    (=>
      (and
        (main@_bb B E H F A)
        (and (or (not K) (not D) (not C))
     (or (not O) (= N (= M 0)))
     (or (not O) (and L O))
     (or (not O) N)
     (or (not P) (and P O))
     (or (not Q) (and Q P))
     (or (not R) (and R Q))
     (or (not K) (= I (>= G H)))
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
