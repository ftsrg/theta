(set-logic HORN)


(declare-fun |INV_MAIN_0| ( Int Int Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (not (= A 0)) (or (not (= E B)) (= F C)) (= D A))
      )
      (INV_MAIN_0 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (let ((a!1 (and (or (not (= E (- 9))) (= F C)) (not (= C 0)))))
  (and (not (= A 0))
       (or (not (= E (- 9))) (not (= F 0)))
       (or (not (= E B)) (= F C))
       (or (not (= B (- 9))) a!1)
       (= D A)))
      )
      (INV_MAIN_0 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (<= F (- 1))) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= F (- 1))) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (<= F (- 1))) a!1 (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= F (- 1))) a!1 (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= F C)) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (<= F C)) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= F C)) a!1 (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) a!1 (not (<= F C)) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) a!1 (not (<= C (- 1))) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= C (- 1))) a!1 (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (<= C (- 1))) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= C (- 1))) (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) a!1 (not (<= A 0)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= Q (- 9))
     (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (<= S 0))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (not (= R (- 1))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (not (= I R))
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (<= S 0))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (= Q (- 9)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (not (= I (- 1)))
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (<= S 0))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (= Q (- 9)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (<= S 0))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (= Q (- 9)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (and (= E (- 9)) (= B (- 9)) (not (<= A 0)) (not (= F C)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= A 1)) (not (<= F (- 1))) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= F (- 1))) (not (>= A 1)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= F (- 1))) (not (>= A 1)) a!1 (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= A 1)) (not (<= F (- 1))) a!1 (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= F C)) (not (>= A 1)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= A 1)) (not (<= F C)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= F C)) (not (>= A 1)) a!1 (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= A 1)) a!1 (not (<= F C)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= C (- 1))) (not (>= A 1)) a!1 (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= A 1)) a!1 (not (<= C (- 1))) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= A 1)) (not (<= C (- 1))) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= C (- 1))) (not (>= A 1)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (<= F (+ C A (* (- 1) D))))))
  (and (= B (- 9)) (not (>= A 1)) a!1 (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (>= (+ F D (* (- 1) C) (* (- 1) A)) 0))))
  (and (= B (- 9)) a!1 (not (>= A 1)) (= E (- 9))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= Q (- 9))
     (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (>= S 1))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (not (= R (- 1))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (not (= I R))
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (>= S 1))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (= Q (- 9)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (not (= I (- 1)))
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (>= S 1))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (= Q (- 9)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (INV_MAIN_0 S T U V W X)
        (INV_MAIN_0 M N O P Q R)
        (INV_MAIN_0 G H I J K L)
        (and (= P V)
     (= O U)
     (= N T)
     (= M S)
     (= L X)
     (= K T)
     (= J V)
     (= H (- 9))
     (= G S)
     (= F R)
     (= E (- 9))
     (= D V)
     (= C I)
     (= B (- 9))
     (= A S)
     (not (= X U))
     (= W T)
     (not (>= S 1))
     (or (not (= T (- 9))) (= R X))
     (or (not (= T (- 9))) (= I U))
     (= Q (- 9)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (and (= E (- 9)) (= B (- 9)) (not (>= A 1)) (not (= F C)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
