(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (and (= (select B C) 0)
     (not (= (select E F) 0))
     (= (select E F) (select E D))
     (= C F)
     (= A D)
     (= B E))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (and (not (= (select B A) 0))
     (not (= (select B A) (select B C)))
     (not (= (select E F) 0))
     (= (select E F) (select E D))
     (= C D)
     (= A F)
     (= B E))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (and (not (= (select B A) 0))
     (= (select B A) (select B C))
     (= (select E F) 0)
     (= (select E F) (select E D))
     (= C D)
     (= A F)
     (= B E))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (and (not (= (select B A) 0))
     (= (select B A) (select B C))
     (not (= (select E D) (select E F)))
     (= C F)
     (= A D)
     (= B E))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select E C) (* (- 1) (select E D))) 0)))
  (and (= (select E C) 0)
       (= (select F B) 0)
       (= (select F B) (select F A))
       (= C B)
       (= D A)
       (or (not a!1) (not (= E F)))
       (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select E A) (* (- 1) (select E B)))
              (+ (select F C) (* (- 1) (select F D))))))
  (and (= (select E A) 0)
       (not (= (select F C) (select F D)))
       (= B D)
       (= A C)
       (or (not (= E F)) (not a!1))
       (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select E C) (* (- 1) (select E D))) 0)))
  (and (not (= (select E C) 0))
       (not (= (select E C) (select E D)))
       (= (select F B) 0)
       (= (select F B) (select F A))
       (= C B)
       (= D A)
       (or (not a!1) (not (= E F)))
       (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select E A) (* (- 1) (select E B)))
              (+ (select F C) (* (- 1) (select F D))))))
  (and (not (= (select E A) 0))
       (not (= (select E A) (select E B)))
       (not (= (select F C) (select F D)))
       (= B D)
       (= A C)
       (or (not (= E F)) (not a!1))
       (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select L K) 0))
     (= (select L K) (select L J))
     (not (= (select I G) 0))
     (= (select I G) (select I H))
     (= F (select I G))
     (= E (select I H))
     (= D (+ 1 G))
     (= H J)
     (= G K)
     (= C (+ 1 H))
     (= B (+ 1 J))
     (= A (+ 1 K))
     (= I L))
      )
      (INV_MAIN_42 F E D C I B A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E F G C D H)
        (let ((a!1 (= (+ (select G E) (* (- 1) (select G F))) 0)))
  (and (= (select H D) 0)
       (= (select H D) (select H C))
       (or (not a!1) (not (= G H)))
       (= (select G E) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D G F E H)
        (let ((a!1 (= (+ (select G C) (* (- 1) (select G D)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select H E) (select H F)))
       (or (not (= G H)) (not a!1))
       (= (select G C) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E F G C D H)
        (let ((a!1 (= (+ (select G E) (* (- 1) (select G F))) 0)))
  (and (not (= (select G E) (select G F)))
       (= (select H D) 0)
       (= (select H D) (select H C))
       (or (not a!1) (not (= G H)))
       (not (= (select G E) 0))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D G F E H)
        (let ((a!1 (= (+ (select G C) (* (- 1) (select G D)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select G C) (select G D)))
       (not (= (select H E) (select H F)))
       (or (not (= G H)) (not a!1))
       (not (= (select G C) 0))))
      )
      END_QUERY
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
     (= B (+ 1 L))
     (= A (+ 1 M))
     (= F (select K I))
     (= E (select K J))
     (= D (+ 1 I))
     (= C (+ 1 J))
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
       (= D (select I G))
       (= C (select I H))
       (= B (+ 1 G))
       (= A (+ 1 H))
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
       (= B (+ 1 H))
       (= A (+ 1 I))
       a!1
       (not (= (select J I) 0))))
      )
      (INV_MAIN_42 C D E F G B A J)
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
