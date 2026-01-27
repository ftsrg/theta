(set-logic HORN)


(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select L J) 0))
     (= (select L J) (select L K))
     (not (= (select I G) 0))
     (= (select I G) (select I H))
     (= A (+ 1 J))
     (= B (+ 1 K))
     (= C (+ 1 H))
     (= D (+ 1 G))
     (= F (select I G))
     (= E (select I H))
     (= H K)
     (= G J)
     (= I L))
      )
      (INV_MAIN_42 F E D C I B A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 G H I J K L M N)
        (and (= (select N M) (select N L))
     (not (= (select K I) 0))
     (= (select K I) (select K J))
     (= A (+ 1 M))
     (= B (+ 1 L))
     (= C (+ 1 J))
     (= D (+ 1 I))
     (= E (select K J))
     (= F (select K I))
     (not (= (select N M) 0)))
      )
      (INV_MAIN_42 F E D C K B A N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J K L)
        (let ((a!1 (or (not (= (select L K) (select L J))) (= (select L K) 0))))
  (and (= (select I G) (select I H))
       (= A (+ 1 H))
       (= B (+ 1 G))
       (= C (select I H))
       (= D (select I G))
       a!1
       (not (= (select I G) 0))))
      )
      (INV_MAIN_42 D C B A I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (or (not (= (select G E) (select G F))) (= (select G E) 0))))
  (and (= (select J I) (select J H))
       (= A (+ 1 I))
       (= B (+ 1 H))
       a!1
       (not (= (select J I) 0))))
      )
      (INV_MAIN_42 C D E F G B A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select F D) 0))
     (= (select F D) (select F E))
     (= (select C A) 0)
     (= B E)
     (= A D)
     (= C F))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select F D) 0))
     (= (select F D) (select F E))
     (not (= (select C A) 0))
     (not (= (select C A) (select C B)))
     (= B E)
     (= A D)
     (= C F))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= (select F D) 0)
     (= (select F D) (select F E))
     (not (= (select C A) 0))
     (= (select C A) (select C B))
     (= B E)
     (= A D)
     (= C F))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select F D) (select F E)))
     (not (= (select C A) 0))
     (= (select C A) (select C B))
     (= B E)
     (= A D)
     (= C F))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select C A) (* (- 1) (select C B))) 0)))
  (and (= (select F D) 0)
       (= (select F D) (select F E))
       (= (select C A) 0)
       (= B E)
       (= A D)
       (or (not a!1) (not (= C F)))
       (= C F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select C A) (* (- 1) (select C B)))
              (+ (select F D) (* (- 1) (select F E))))))
  (and (not (= (select F D) (select F E)))
       (= (select C A) 0)
       (= B E)
       (= A D)
       (or (not (= C F)) (not a!1))
       (= C F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select C A) (* (- 1) (select C B))) 0)))
  (and (= (select F D) 0)
       (= (select F D) (select F E))
       (not (= (select C A) 0))
       (not (= (select C A) (select C B)))
       (= B E)
       (= A D)
       (or (not a!1) (not (= C F)))
       (= C F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select C A) (* (- 1) (select C B)))
              (+ (select F D) (* (- 1) (select F E))))))
  (and (not (= (select F D) (select F E)))
       (not (= (select C A) 0))
       (not (= (select C A) (select C B)))
       (= B E)
       (= A D)
       (or (not (= C F)) (not a!1))
       (= C F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (let ((a!1 (= (+ (select E C) (* (- 1) (select E D))) 0)))
  (and (= (select H G) (select H F))
       (= (select E C) 0)
       (or (not a!1) (not (= E H)))
       (= (select H G) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (let ((a!1 (= (+ (select E C) (* (- 1) (select E D)))
              (+ (select H G) (* (- 1) (select H F))))))
  (and (= (select E C) 0)
       (or (not (= E H)) (not a!1))
       (not (= (select H G) (select H F)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (let ((a!1 (= (+ (select E C) (* (- 1) (select E D))) 0)))
  (and (= (select H G) (select H F))
       (not (= (select E C) 0))
       (not (= (select E C) (select E D)))
       (or (not a!1) (not (= E H)))
       (= (select H G) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (let ((a!1 (= (+ (select E C) (* (- 1) (select E D)))
              (+ (select H G) (* (- 1) (select H F))))))
  (and (not (= (select E C) 0))
       (not (= (select E C) (select E D)))
       (or (not (= E H)) (not a!1))
       (not (= (select H G) (select H F)))))
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
