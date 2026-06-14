(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F))
      )
      (INV_MAIN_0 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (INV_MAIN_0 A D C B F E)
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
        (INV_MAIN_0 A D C B F E)
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
        (INV_MAIN_0 A C E B D F)
        (and (= (select E C) 0) (= (select F D) 0) (not (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (and (not (= (select C B) 0)) (not (= (select F E) 0)) (= v_6 A) (= 0 v_7))
      )
      (INV_MAIN_1 A v_6 B C D v_7 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 C A E D G H B F)
        (and (= (select D C) (select D E))
     (= (select F (+ G H)) 0)
     (not (= (select D C) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 D A B C G H E F)
        (let ((a!1 (not (= (select F (+ G H)) 0))))
  (and a!1 (= (select F E) (select F (+ G H))) (= (select C D) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B A E G C D F H)
        (let ((a!1 (not (= (select H (+ C D)) 0))))
  (and (= (select G B) (select G E))
       a!1
       (= (select H F) (select H (+ C D)))
       (or (not (= G H)) (not (= E F)))
       (not (= (select G B) 0))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C E F G H D I J)
        (and (= (select G C) 0) (= A (+ 1 I)) (= B (+ 1 F)) (= (select J (+ H D)) 0))
      )
      (INV_MAIN_0 E B G H A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J)
        (let ((a!1 (not (= (select J (+ G H)) 0)))
      (a!2 (not (= (select J I) (select J (+ G H))))))
  (and (not (= (select F C) (select F E)))
       a!1
       a!2
       (= A (+ 1 H))
       (= B (+ 1 C))
       (not (= (select F C) 0))))
      )
      (INV_MAIN_1 B D E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I)
        (let ((a!1 (or (= (select I H) (select I (+ F G))) (= (select I (+ F G)) 0))))
  (and (not (= (select E B) (select E D)))
       (= A (+ 1 B))
       a!1
       (not (= (select E B) 0))))
      )
      (INV_MAIN_1 A C D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I)
        (let ((a!1 (not (= (select I H) (select I (+ F G)))))
      (a!2 (not (= (select I (+ F G)) 0))))
  (and a!1
       (= A (+ 1 G))
       (or (= (select E B) (select E D)) (= (select E B) 0))
       a!2))
      )
      (INV_MAIN_1 B C D E F A H I)
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
