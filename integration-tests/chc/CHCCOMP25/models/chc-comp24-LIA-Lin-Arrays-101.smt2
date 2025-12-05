(set-logic HORN)


(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F))
      )
      (INV_MAIN_0 B A C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (INV_MAIN_0 C D E F G H)
        (and (not (= (select E D) 0))
     (= B (select H F))
     (= A (+ 1 F))
     (not (= (select H F) 0))
     (= 0 v_8)
     (= v_9 G))
      )
      (INV_MAIN_1 C v_8 D E B A G v_9 H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I J)
        (and (= (select J I) 0) (= A (+ 1 D)) (= (select E (+ B C)) 0))
      )
      (INV_MAIN_0 B A E G H J)
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
       (= A (+ 1 J))
       (= B (+ 1 D))
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
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (and (= (select C B) 0) (not (= (select F D) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (and (not (= (select C B) 0)) (= (select F D) 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (and (= (select F D) 0) (= (select C B) 0) (not (= C F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H I)
        (let ((a!1 (not (= (select D (+ A B)) 0))))
  (and (= (select D C) (select D (+ A B))) (= (select I H) 0) a!1))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H I)
        (and (not (= (select I H) 0)) (= (select I H) E) (= (select D (+ A B)) 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H I)
        (let ((a!1 (or (not (= C (+ (- 1) F))) (not (= D I))))
      (a!2 (not (= (select D (+ A B)) 0))))
  (and (= (select D C) (select D (+ A B)))
       (not (= (select I H) 0))
       (= (select I H) E)
       a!1
       a!2))
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
