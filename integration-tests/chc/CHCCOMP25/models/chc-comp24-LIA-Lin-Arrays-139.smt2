(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (and (= (select B C) D)
     (not (= (select F G) H))
     (= D H)
     (not (= E 0))
     (= C G)
     (not (= A 0))
     (= A E)
     (= B F))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (and (not (= (select F G) H))
     (= D 0)
     (= D E)
     (not (= E 0))
     (= B H)
     (= A G)
     (= C F))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (and (not (= (select B C) D))
     (= (select F G) H)
     (= D H)
     (not (= E 0))
     (= C G)
     (not (= A 0))
     (= A E)
     (= B F))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (not (= (select E F) G))
     (not (= D 0))
     (= D H)
     (= H 0)
     (= G B)
     (= F A)
     (= E C))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select G E) B)
     (= (select H F) D)
     (= E F)
     (not (= C 0))
     (= B D)
     (not (= A 0))
     (= A C)
     (or (not (= E F)) (not (= G H)))
     (= G H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select G F) D)
     (= D B)
     (= F A)
     (= E 0)
     (not (= C 0))
     (= C E)
     (or (not (= F 0)) (not (= G H)))
     (= G H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select H F) E)
     (not (= D 0))
     (= C 0)
     (= C D)
     (= B E)
     (= A F)
     (or (not (= G H)) (not (= 0 F)))
     (= G H))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select J H) G))
     (not (= (select F E) C))
     (= B (+ (- 1) D))
     (not (= I 0))
     (= E H)
     (not (= D 0))
     (= D I)
     (= C G)
     (= A (+ 1 H))
     (= F J))
      )
      (INV_MAIN_42 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 B A E G D F C H)
        (let ((a!1 (or (not (= G H)) (not (= E (+ (- 1) F))))))
  (and (= (select H F) D)
       (not (= C 1))
       (not (= A 0))
       a!1
       (= (select G (+ 1 E)) B)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D C F G A B E H)
        (and (= E 1)
     (not (= C 0))
     (or (not (= G H)) (not (= F (- 1))))
     (= (select G (+ 1 F)) D))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C B G E F D H)
        (and (not (= D 1)) (= C 0) (or (not (= G H)) (not (= 0 F))) (= (select H F) E))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A E B G C D F H)
        (and (= F 1) (= E 0) (not (= G H)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J K L)
        (let ((a!1 (not (= (select H (+ 1 G)) E))))
  (and a!1
       (= D (+ (- 1) F))
       (not (= K 1))
       (not (= F 0))
       (= C (+ 1 G))
       (= B (+ 1 J))
       (= A (+ (- 1) K))
       (not (= (select L J) I))))
      )
      (INV_MAIN_42 E D C H I B A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (not (= (select F (+ 1 E)) C))))
  (and (= B (+ (- 1) D))
       (not (= D 0))
       (= A (+ 1 E))
       (or (= I 1) (= (select J H) G))
       a!1))
      )
      (INV_MAIN_42 C B A F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (or (= D 0) (= (select F (+ 1 E)) C))))
  (and (= B (+ 1 H))
       (not (= I 1))
       (= A (+ (- 1) I))
       a!1
       (not (= (select J H) G))))
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
