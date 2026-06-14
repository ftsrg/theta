(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_0| ( Int (Array Int Int) Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int Int)) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= (select C (- 9)) 0)
     (= (select B (- 9)) 0)
     (not (= H 0))
     (= A H)
     (<= 0 G)
     (not (<= 0 F))
     (or (not (= B C)) (and (= F G) (= D E)))
     (= B C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) ) 
    (=>
      (and
        (and (not (= (select C (- 9)) 0))
     (= (select B (- 9)) 0)
     (not (= D 0))
     (= A D)
     (not (<= 0 E))
     (= B C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= (select A (- 9)) 0)
     (= (select B (- 9)) 0)
     (not (= H 0))
     (= F 0)
     (= F H)
     (<= 0 G)
     (<= 0 E)
     (or (and (= E G) (= C D)) (not (= A B)))
     (= A B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (and (not (= (select B (- 9)) 0))
     (= (select A (- 9)) 0)
     (= E 0)
     (= E C)
     (not (= C 0))
     (<= 0 D)
     (= A B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) ) 
    (=>
      (and
        (and (= (select C (- 9)) 0)
     (not (= (select A (- 9)) 0))
     (not (= E 0))
     (= B 0)
     (= B E)
     (<= 0 D)
     (= A C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) ) 
    (=>
      (and
        (and (not (= (select A (- 9)) 0))
     (not (= (select C (- 9)) 0))
     (not (= D 0))
     (= B 0)
     (= B D)
     (= A C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int Int)) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= (select C (- 9)) 0)
     (= (select B (- 9)) 0)
     (not (= G 0))
     (= G A)
     (not (<= 0 H))
     (<= 0 F)
     (or (not (= B C)) (and (= F H) (= D E)))
     (= B C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C (Array Int Int)) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= (select A (- 9)) 0)
     (= (select B (- 9)) 0)
     (= H 0)
     (not (= F 0))
     (= F H)
     (<= 0 G)
     (<= 0 E)
     (or (and (= E G) (= C D)) (not (= A B)))
     (= A B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (and (not (= (select B (- 9)) 0))
     (= (select A (- 9)) 0)
     (not (= E 0))
     (= E C)
     (= C 0)
     (<= 0 D)
     (= A B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) (E Int) ) 
    (=>
      (and
        (and (not (= (select B (- 9)) 0))
     (= (select D (- 9)) 0)
     (not (= C 0))
     (= C A)
     (not (<= 0 E))
     (= B D))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) ) 
    (=>
      (and
        (and (= (select C (- 9)) 0)
     (not (= (select A (- 9)) 0))
     (= E 0)
     (not (= B 0))
     (= B E)
     (<= 0 D)
     (= A C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) ) 
    (=>
      (and
        (and (not (= (select A (- 9)) 0))
     (not (= (select C (- 9)) 0))
     (= D 0)
     (not (= B 0))
     (= B D)
     (= A C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (and (not (= G H))
     (= (select C (- 9)) 0)
     (= (select D (- 9)) 0)
     (= A B)
     (not (<= 0 F))
     (not (<= 0 E))
     (or (and (= E F) (= G H)) (not (= C D)))
     (= C D))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= G H)) (not (= (- 1) (select H (- 9)))))))
  (and (= (select C (- 9)) 0)
       (= (select B (- 9)) 0)
       (= F 0)
       (= A F)
       (not (<= 0 D))
       (<= 0 E)
       a!1
       (or (not (= B C)) (and (= D E) (= G H)))
       (= B C)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= E F)) (not (= (- 1) (select F (- 9)))))))
  (and (not (= (select F (- 9)) 0))
       (= (select B (- 9)) 0)
       (= C 0)
       (= A C)
       (not (<= 0 D))
       a!1
       (= B F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= G H)) (not (= (select G (- 9)) (- 1))))))
  (and (= (select C (- 9)) 0)
       (= (select B (- 9)) 0)
       (= E 0)
       (= E A)
       (<= 0 D)
       (not (<= 0 F))
       a!1
       (or (not (= B C)) (and (= D F) (= G H)))
       (= B C)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= G H)) (not (= (select G (- 9)) (select H (- 9)))))))
  (and (= (select A (- 9)) 0)
       (= (select B (- 9)) 0)
       (= D 0)
       (= D F)
       (= F 0)
       (<= 0 E)
       (<= 0 C)
       a!1
       (or (and (= C E) (= G H)) (not (= A B)))
       (= A B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= E F)) (not (= (select E (- 9)) (select F (- 9)))))))
  (and (= (select A (- 9)) 0)
       (not (= (select F (- 9)) 0))
       (= B 0)
       (= D 0)
       (= D B)
       (<= 0 C)
       a!1
       (= A F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= E F)) (not (= (select E (- 9)) (- 1))))))
  (and (= (select C (- 9)) 0)
       (not (= (select E (- 9)) 0))
       (= B 0)
       (= B A)
       (not (<= 0 D))
       a!1
       (= E C)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= E F)) (not (= (select E (- 9)) (select F (- 9)))))))
  (and (not (= (select E (- 9)) 0))
       (= (select B (- 9)) 0)
       (= D 0)
       (= A 0)
       (= A D)
       (<= 0 C)
       a!1
       (= E B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (or (not (= C D)) (not (= (select C (- 9)) (select D (- 9)))))))
  (and (not (= (select D (- 9)) 0))
       (not (= (select C (- 9)) 0))
       (= B 0)
       (= A 0)
       (= A B)
       a!1
       (= C D)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select A (- 9)) 0)
     (= (select B (- 9)) 0)
     (not (= G 0))
     (not (= E 0))
     (= E G)
     (<= 0 D)
     (<= 0 C)
     (or (and (= C D) (= F H)) (not (= A B)))
     (= A B))
      )
      (INV_MAIN_0 E F G H)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= (select A (- 9)) 0)
     (not (= (select F (- 9)) 0))
     (not (= E 0))
     (not (= C 0))
     (= C E)
     (<= 0 B)
     (= A F))
      )
      (INV_MAIN_0 C D E F)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= (select A (- 9)) 0)
     (not (= (select D (- 9)) 0))
     (not (= E 0))
     (not (= C 0))
     (= C E)
     (<= 0 B)
     (= D A))
      )
      (INV_MAIN_0 C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select B (- 9)) 0))
     (not (= (select D (- 9)) 0))
     (not (= C 0))
     (not (= A 0))
     (= A C)
     (= B D))
      )
      (INV_MAIN_0 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F (Array Int Int)) (G (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 B C A E)
        (let ((a!1 (and (<= 0 D) (not (= (select E (- 9)) (- 1))))))
  (and (not (<= B 0)) (or (not (= F G)) a!1) (not (<= 0 B))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A D B F)
        (let ((a!1 (not (= (+ (select D (- 9)) A) (+ (select F (- 9)) B))))
      (a!2 (not (= (ite (<= 0 C) (select D (- 9)) (- 1))
                   (ite (<= 0 E) (select F (- 9)) (- 1))))))
  (and (not (<= A 0))
       (or (and (= C E) (= G H)) a!1 (not (= D F)))
       (or (not (= G H)) a!2)
       (<= 0 A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A D B F)
        (let ((a!1 (not (= (+ (select D (- 9)) A) (+ (select F (- 9)) B))))
      (a!2 (not (= (ite (<= 0 C) (select D (- 9)) (- 1))
                   (ite (<= 0 E) (select F (- 9)) (- 1))))))
  (and (or (and (= C E) (= G H)) a!1 (not (= D F)))
       (or (not (= G H)) a!2)
       (<= A 0)))
      )
      END_QUERY
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
