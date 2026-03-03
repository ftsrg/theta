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
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        main@entry
        (let ((a!1 (= B (or (not (<= J 1073741823)) (not (>= J 0)))))
      (a!2 (= A (or (not (<= I 1073741823)) (not (>= I 0))))))
  (and a!1
       (= D (= J 0))
       (or (not G) (not D) (not C))
       (or (not G) (not F) (= E J))
       (or (not G) (not F) (= H I))
       (or (not G) (not F) (= K E))
       (or (not G) (not F) (= L H))
       (or (not F) (and G F))
       (or (not G) (and G C))
       (not A)
       (not B)
       (= F true)
       a!2))
      )
      (main@.lr.ph.i I J K L)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Int) (L Int) (M Bool) (N Int) (O Bool) (P Int) (Q Int) (R Int) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) ) 
    (=>
      (and
        (main@.lr.ph.i V W D C)
        (and (or (not J) (not B) (not A))
     (or (not M) B (not A))
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
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Bool) ) 
    (=>
      (and
        main@entry
        (let ((a!1 (= B (or (not (<= G 1073741823)) (not (>= G 0)))))
      (a!2 (or (not K) (= I (+ F (* (- 1) G)))))
      (a!3 (= A (or (not (<= F 1073741823)) (not (>= F 0))))))
  (and a!1
       (= C (= G 0))
       (or (not D) (= E F) (not K))
       (or (not D) (= H E) (not K))
       (or (not D) C (not K))
       a!2
       (or (not K) (= J (= H I)))
       (or (not K) (and D K))
       (or (not K) (not J))
       (or (not L) (and L K))
       (= L true)
       (not A)
       (not B)
       a!3))
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
       (or (not U) (= V T) (not B1))
       (or (not U) (= Y V) (not B1))
       (or (not U) (not R) (= S Q))
       (or (not U) (not R) (= T S))
       (or (not U) (not R) P)
       (or (not J) (= E (+ (- 1) C)))
       (or (not J) (= F (+ 1 D)))
       (or (not J) (and J A))
       (or (not M) (= G (+ 1 C)))
       (or (not M) (= H (+ (- 1) D)))
       (or (not M) (and M A))
       a!1
       (or (not B1) (= A1 (= Y Z)))
       (or (not B1) (and U B1))
       (or (not B1) (not A1))
       (or (not C1) (and C1 B1))
       (or (not R) (= P (= O 0)))
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
