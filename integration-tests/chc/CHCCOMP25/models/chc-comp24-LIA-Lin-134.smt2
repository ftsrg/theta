(set-logic HORN)


(declare-fun |fail$unknown:25| ( Int ) Bool)
(declare-fun |f_1034$unknown:23| ( Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |omega_1032$unknown:33| ( Int Int Int ) Bool)
(declare-fun |f_1034$unknown:19| ( Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) ) 
    (=>
      (and
        (and (= M 0)
     (= L 0)
     (= K 0)
     (= J 0)
     (= I 0)
     (= H 0)
     (= G 0)
     (= F 0)
     (= E 0)
     (= D 0)
     (= C 0)
     (= B 0)
     (= A 0)
     (= S 0)
     (= R 0)
     (= Q 0)
     (= P 0)
     (= O 0)
     (= W 1)
     (= V 0)
     (= U 0)
     (= T 0)
     (= N 0))
      )
      (|f_1034$unknown:23| W V U T S A R Q P O B N M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (|f_1034$unknown:23| M L K J I H G F E D C B A)
        true
      )
      (|f_1034$unknown:19| M L K J I H G F E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) ) 
    (=>
      (and
        (|f_1034$unknown:19| A B V N M E L K J I F H G)
        (and (= L 0)
     (= K 0)
     (= J 0)
     (= I 0)
     (= H 0)
     (= G 0)
     (= F 0)
     (= E 0)
     (= D 0)
     (= C 0)
     (= R 0)
     (= Q 0)
     (= P 0)
     (= O 0)
     (= N 0)
     (= U 1)
     (= T 0)
     (= S 0)
     (= M 0))
      )
      (|omega_1032$unknown:33| A B V)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|omega_1032$unknown:33| C B A)
        (and (= D 1) (not (= 0 A)))
      )
      (|fail$unknown:25| D)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (|fail$unknown:25| A)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
