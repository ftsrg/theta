(set-logic HORN)


(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)
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
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A D C F B E)
        (and (= (select C D) 0) (not (= (select E F) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A D C F B E)
        (and (not (= (select C D) 0)) (= (select E F) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A C E D B F)
        (and (= (select E C) 0) (= (select F D) 0) (not (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (INV_MAIN_0 C D E F G H)
        (and (not (= (select E D) 0))
     (= A (+ 1 F))
     (= B (select H F))
     (not (= (select H F) 0))
     (= 0 v_8)
     (= v_9 G))
      )
      (INV_MAIN_1 C v_8 D E B A G v_9 H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) (I Int) ) 
    (=>
      (and
        (INV_MAIN_1 F G D E A B C I H)
        (let ((a!1 (not (= (select E (+ F G)) 0))))
  (and (= (select E D) (select E (+ F G))) (= (select H I) 0) a!1))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_1 E F A D I B C H G)
        (and (not (= (select G H) 0)) (= (select G H) I) (= (select D (+ E F)) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C F H E G A D I)
        (let ((a!1 (or (not (= H I)) (not (= F (+ (- 1) G)))))
      (a!2 (not (= (select H (+ B C)) 0))))
  (and (= (select H F) (select H (+ B C)))
       (not (= (select I D) 0))
       (= (select I D) E)
       a!1
       a!2))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E C F G B H I D J)
        (and (= (select G (+ E C)) 0) (= A (+ 1 F)) (= (select J D) 0))
      )
      (INV_MAIN_0 E A G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J K)
        (let ((a!1 (not (= (select F E) (select F (+ C D)))))
      (a!2 (not (= (select F (+ C D)) 0))))
  (and a!1
       (not (= (select K J) 0))
       (not (= (select K J) G))
       (= B (+ 1 D))
       (= A (+ 1 J))
       a!2))
      )
      (INV_MAIN_1 C B E F G H I A K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I J)
        (let ((a!1 (not (= (select E D) (select E (+ B C)))))
      (a!2 (not (= (select E (+ B C)) 0))))
  (and a!1 (= A (+ 1 C)) (or (= (select J I) F) (= (select J I) 0)) a!2))
      )
      (INV_MAIN_1 B A D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I J)
        (let ((a!1 (or (= (select E D) (select E (+ B C))) (= (select E (+ B C)) 0))))
  (and (not (= (select J I) F)) (= A (+ 1 I)) a!1 (not (= (select J I) 0))))
      )
      (INV_MAIN_1 B C D E F G H A J)
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
