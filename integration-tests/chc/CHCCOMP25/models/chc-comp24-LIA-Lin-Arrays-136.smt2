(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select G H) (* (- 1) (select G F))) 0)))
  (and (not (= (select G H) 0))
       (not (= 0 E))
       a!1
       (= D 0)
       (= D E)
       (= B F)
       (= A H)
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select G H) (* (- 1) (select G F))) 0)))
  (and (not (= (select C B) (select C D)))
       (not (= (select G H) 0))
       (not (= 0 E))
       a!1
       (= D F)
       (= B H)
       (not (= A 0))
       (= A E)
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select G H) (* (- 1) (select G F))) 0)))
  (and (= (select C D) (select C B))
       (= (select C D) 0)
       (not (= (select G H) 0))
       (not (= 0 E))
       a!1
       (= D H)
       (= B F)
       (not (= A 0))
       (= A E)
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select G F) (* (- 1) (select G H))) 0)))
  (and (= (select C D) (select C B))
       (not (= (select C D) 0))
       (not (= 0 E))
       (not a!1)
       (= D F)
       (= B H)
       (not (= A 0))
       (= A E)
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select G H) (* (- 1) (select G F))) 0)))
  (and (= (select C D) (select C B))
       (not (= (select C D) 0))
       (= (select G H) 0)
       (not (= 0 E))
       a!1
       (= D H)
       (= B F)
       (not (= A 0))
       (= A E)
       (= C G)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= (select E F) (select E D))
     (not (= (select E F) 0))
     (= 0 H)
     (= D A)
     (= F G)
     (not (= C 0))
     (= C H)
     (= E B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= 0 D))
       (not a!1)
       (= C 0)
       (= C D)
       (= B F)
       (= A E)
       (or (not a!2) (not (= G H)))
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0))
      (a!2 (= (+ (select G C) (* (- 1) (select G D)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select G C) (select G D)))
       (not (= 0 B))
       (not a!1)
       (= D F)
       (= C E)
       (not (= A 0))
       (= A B)
       (or (not (= G H)) (not a!2))
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H D) (* (- 1) (select H C))) 0))
      (a!2 (= (+ (select G E) (* (- 1) (select G F))) 0)))
  (and (not (= (select G E) (select G F)))
       (= (select H D) 0)
       (not (= 0 B))
       a!1
       (= F C)
       (= E D)
       (not (= A 0))
       (= A B)
       (or (not (= G H)) (not a!2))
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select G E) (* (- 1) (select G F))) 0)))
  (and (not (= (select G E) (select G F)))
       (= 0 D)
       (= F A)
       (= E C)
       (not (= B 0))
       (= B D)
       (or (not (= G H)) (not a!1))
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select G C) (select G B))
       (= (select G C) 0)
       (not (= 0 D))
       (not a!1)
       (= C E)
       (= B F)
       (not (= A 0))
       (= A D)
       (or (not a!2) (not (= G H)))
       (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select K H) (* (- 1) (select K J))) 0)))
  (and (not (= (select K H) 0))
       (= (select G E) (select G D))
       (not (= (select G E) 0))
       (not (= 0 I))
       a!1
       (= B (+ 1 E))
       (= C (+ 1 D))
       (= A (+ H I))
       (not (= F 0))
       (= F I)
       (= E H)
       (= D J)
       (= G K)))
      )
      (INV_MAIN_42 C B F G H A J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D C A G E B F H)
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 F))))))
(let ((a!2 (= (+ (select G C) (* (- 1) (select G D))) a!1)))
  (and (not (= a!1 0))
       (not (= E (+ (- 1) B)))
       (not (= A 1))
       (or (not (= G H)) (not a!2))
       (not (= (select G C) (select G D))))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F E A G D B C H)
        (let ((a!1 (+ (select H (+ 1 D)) (* (- 1) (select H (+ 1 C)))))
      (a!2 (= (+ (select G E) (* (- 1) (select G F))) 0)))
  (and (= (select H (+ 1 D)) 0)
       (= a!1 0)
       (not (= D (+ (- 1) B)))
       (not (= A 1))
       (or (not (= G H)) (not a!2))
       (not (= (select G E) (select G F)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F E B G C D A H)
        (let ((a!1 (= (+ (select G E) (* (- 1) (select G F))) 0)))
  (and (= C (+ (- 1) D))
       (not (= B 1))
       (or (not (= G H)) (not a!1))
       (not (= (select G E) (select G F)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 B C A G E D F H)
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 F))))))
  (and (= (select G C) 0)
       (not (= a!1 0))
       (not (= E (+ (- 1) D)))
       (not (= A 1))
       (or (not (= G H)) (not (= 0 a!1)))
       (= (select G C) (select G B))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 B C A G F D E H)
        (let ((a!1 (+ (select H (+ 1 F)) (* (- 1) (select H (+ 1 E))))))
  (and (= (select G C) (select G B))
       (= (select G C) 0)
       (= (select H (+ 1 F)) 0)
       (= a!1 0)
       (not (= F (+ (- 1) D)))
       (not (= A 1))
       (not (= G H))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D B G E F A H)
        (and (= (select G D) (select G C))
     (= (select G D) 0)
     (= E (+ (- 1) F))
     (not (= B 1))
     (not (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C G E D F H)
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 F))))))
  (and (not (= E (+ (- 1) D)))
       (= C 1)
       (or (not (= G H)) (not (= 0 a!1)))
       (not (= a!1 0))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C G F D E H)
        (let ((a!1 (+ (select H (+ 1 F)) (* (- 1) (select H (+ 1 E))))))
  (and (= (select H (+ 1 F)) 0)
       (= a!1 0)
       (not (= F (+ (- 1) D)))
       (= C 1)
       (not (= G H))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B D G E F C H)
        (and (= D 1) (= E (+ (- 1) F)) (not (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F G H I J K L M)
        (let ((a!1 (+ (select M (+ 1 J)) (* (- 1) (select M (+ 1 L)))))
      (a!2 (not (= (select M (+ 1 J)) 0))))
  (and (= (select I G) (select I F))
       (not (= (select I G) 0))
       (= a!1 0)
       (= D (+ 1 G))
       (= E (+ 1 F))
       (= C (+ (- 1) H))
       (not (= J (+ (- 1) K)))
       (not (= H 1))
       (= B (+ 1 J))
       (= A (+ 1 L))
       a!2))
      )
      (INV_MAIN_42 E D C I B K A M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I J K)
        (let ((a!1 (+ (select K (+ 1 H)) (* (- 1) (select K (+ 1 J))))))
(let ((a!2 (or (= H (+ (- 1) I)) (not (= a!1 0)) (= (select K (+ 1 H)) 0))))
  (and (not (= (select G E) 0))
       (= B (+ 1 E))
       (= C (+ 1 D))
       (= A (+ (- 1) F))
       (not (= F 1))
       a!2
       (= (select G E) (select G D)))))
      )
      (INV_MAIN_42 C B A G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (+ (select J (+ 1 G)) (* (- 1) (select J (+ 1 I)))))
      (a!2 (or (= (select F D) 0) (not (= (select F D) (select F C))) (= E 1)))
      (a!3 (not (= (select J (+ 1 G)) 0))))
  (and (= a!1 0) (= A (+ 1 I)) (= B (+ 1 G)) (not (= G (+ (- 1) H))) a!2 a!3))
      )
      (INV_MAIN_42 C D E F B H A J)
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
