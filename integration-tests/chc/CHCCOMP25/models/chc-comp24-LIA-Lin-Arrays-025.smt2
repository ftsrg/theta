(set-logic HORN)


(declare-fun |main@entry| ( Int (Array Int Int) Int ) Bool)
(declare-fun |main@orig.main.exit.split| ( ) Bool)
(declare-fun |main@.lr.ph| ( Int (Array Int Int) Int ) Bool)

(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) ) 
    (=>
      (and
        true
      )
      (main@entry A B C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Bool) (G Bool) (H (Array Int Int)) (I Bool) (J Bool) (K (Array Int Int)) (L Int) (M (Array Int Int)) (N Int) ) 
    (=>
      (and
        (main@entry L A C)
        (and (= B C)
     (= D (store A N 0))
     (= H (store D N E))
     (or (not F) (not J) G)
     (or (not J) (not I) (= K H))
     (or (not J) (not I) (= M K))
     (or (not I) (and J I))
     (or (not J) (and J F))
     (= I true)
     (not (= (<= E 0) G)))
      )
      (main@.lr.ph L M N)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Bool) (F (Array Int Int)) (G Bool) (H Bool) (I (Array Int Int)) (J Int) (K (Array Int Int)) (L Int) ) 
    (=>
      (and
        (main@.lr.ph J B L)
        (and (= D (select B L))
     (= A J)
     (= C (+ (- 1) D))
     (= F (store B L C))
     (or (not H) (not G) (= I F))
     (or (not H) (not G) (= K I))
     (or (not H) (not G) E)
     (or (not G) (and H G))
     (= G true)
     (not (= (<= D 1) E)))
      )
      (main@.lr.ph J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Bool) (I (Array Int Int)) (J Bool) (K (Array Int Int)) (L (Array Int Int)) (M Bool) (N Bool) (O Bool) ) 
    (=>
      (and
        (main@entry A B D)
        (and (= C D)
     (= E (store B F 0))
     (= I (store E F G))
     (or (not J) (not N) (= K L))
     (or (not J) (not N) (= L I))
     (or (not J) (not N) (not H))
     (or (not N) (and J N))
     (or (not N) (not M))
     (or (not O) (and O N))
     (not N)
     (= O true)
     (not (= (<= G 0) H)))
      )
      main@orig.main.exit.split
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I (Array Int Int)) (J Bool) (K (Array Int Int)) (L (Array Int Int)) (M Bool) (N Bool) (O Bool) ) 
    (=>
      (and
        (main@.lr.ph B C D)
        (and (= E (+ (- 1) F))
     (= A B)
     (= F (select C D))
     (= I (store C D E))
     (or (not J) (not N) (= K L))
     (or (not J) (not N) (= L I))
     (or (not J) (not H) (not G))
     (or (not N) (and J N))
     (or (not N) (not M))
     (or (not O) (and O N))
     (or (not J) (and J G))
     (not N)
     (= O true)
     (not (= (<= F 1) H)))
      )
      main@orig.main.exit.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@orig.main.exit.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
