(set-logic HORN)


(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F))
      )
      (INV_MAIN_0 B A C E D F)
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J)
        (and (= (select J (+ G H)) 0) (= A (+ 1 I)) (= B (+ 1 E)) (= (select F C) 0))
      )
      (INV_MAIN_0 D B F G A J)
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
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (and (= (select C B) 0) (not (= (select F E) 0)))
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
        (and (not (= (select C B) 0)) (= (select F E) 0))
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
        (and (= (select F E) 0) (= (select C B) 0) (not (= C F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (and (= (select D A) (select D C))
     (= (select H (+ E F)) 0)
     (not (= (select D A) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (let ((a!1 (not (= (select H (+ E F)) 0))))
  (and a!1 (= (select H G) (select H (+ E F))) (= (select D A) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (let ((a!1 (not (= (select H (+ E F)) 0))))
  (and (= (select D A) (select D C))
       a!1
       (= (select H G) (select H (+ E F)))
       (or (not (= C G)) (not (= D H)))
       (not (= (select D A) 0))))
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
