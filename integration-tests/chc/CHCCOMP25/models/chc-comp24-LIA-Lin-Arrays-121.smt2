(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= B D) (= A E) (= C F))
      )
      (INV_MAIN_0 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A C B F D E)
        (let ((a!1 (not (= (store B A (select B C)) (store E D (select E F))))))
  (and (= (select E F) 0) (or (not (= A D)) a!1) (= (select B C) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K (Array Int Int)) (L Int) ) 
    (=>
      (and
        (INV_MAIN_0 G I H L J K)
        (and (= A (store K J (select K L)))
     (not (= (select H I) 0))
     (not (= (select K L) 0))
     (= F (+ 1 G))
     (= E (+ 1 I))
     (= C (+ 1 L))
     (= B (+ 1 J))
     (= D (store H G (select H I))))
      )
      (INV_MAIN_0 F E D C B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D F E G H I)
        (and (not (= (select E F) 0))
     (= (select I G) 0)
     (= C (+ 1 D))
     (= B (+ 1 F))
     (= A (store E D (select E F))))
      )
      (INV_MAIN_0 C B A G H I)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H (Array Int Int)) (I Int) ) 
    (=>
      (and
        (INV_MAIN_0 D E F I G H)
        (and (not (= (select H I) 0))
     (= (select F E) 0)
     (= C (+ 1 I))
     (= B (+ 1 G))
     (= A (store H G (select H I))))
      )
      (INV_MAIN_0 D E F C B A)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        END_QUERY
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
