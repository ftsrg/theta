(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (v_10 Int) ) 
    (=>
      (and
        (and (= B (+ (- 4) G))
     (= A (+ (- 4) H))
     (= E I)
     (= D H)
     (= C G)
     (= F J)
     (= 0 v_10))
      )
      (INV_MAIN_42 C v_10 E D F B I A J)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) (N Int) (O (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 G H I J K L M N O)
        (let ((a!1 (store K (+ G (* 4 H)) (select K (+ J (* 4 H)))))
      (a!2 (= A (store O (+ 4 L) (select O (+ 4 N))))))
  (and (= E a!1)
       (= B (+ 4 N))
       (= C (+ (- 1) M))
       (= D (+ 4 L))
       (= F (+ 1 H))
       (not (<= M 0))
       (not (<= I H))
       a!2))
      )
      (INV_MAIN_42 G F I J E D C B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J K)
        (let ((a!1 (store G (+ C (* 4 D)) (select G (+ F (* 4 D))))))
  (and (= B (+ 1 D)) (<= I 0) (not (<= E D)) (= A a!1)))
      )
      (INV_MAIN_42 C B E F A H I J K)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J K L M)
        (let ((a!1 (= A (store M (+ 4 J) (select M (+ 4 L))))))
  (and (= C (+ (- 1) K))
       (= B (+ 4 L))
       (= D (+ 4 J))
       (not (<= K 0))
       (<= G F)
       a!1))
      )
      (INV_MAIN_42 E F G H I D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H I)
        (and (<= G 0) (<= C B) (not (= E I)))
      )
      false
    )
  )
)

(check-sat)
(exit)
