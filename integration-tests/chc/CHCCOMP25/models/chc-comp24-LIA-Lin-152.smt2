(set-logic HORN)


(declare-fun |INV_MAIN_2| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_4| ( Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_3| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (= D 1) (= C 1) (= B E) (= A 1) (= F 1))
      )
      (INV_MAIN_1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_1 G B H I E J)
        (and (= I (+ (- 1) D)) (= H C) (= G (+ (- 1) A)) (>= B G) (>= E I) (= J F))
      )
      (INV_MAIN_1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 G B H D E F)
        (and (= G (+ (- 1) A)) (>= B G) (not (>= E D)) (= H C))
      )
      (INV_MAIN_1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A B C G E H)
        (and (= G (+ (- 1) D)) (not (>= B A)) (>= E G) (= H F))
      )
      (INV_MAIN_1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 H B C G E F)
        (and (= D 1) (not (>= B H)) (not (>= E G)) (= A 0))
      )
      (INV_MAIN_2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_2 G B H I E J)
        (and (= (+ H G) C)
     (= I (+ (- 1) D))
     (= G (+ (- 1) A))
     (>= B G)
     (>= E I)
     (= (+ J I) F))
      )
      (INV_MAIN_2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 G B H D E F)
        (and (= G (+ (- 1) A)) (>= B G) (not (>= E D)) (= (+ H G) C))
      )
      (INV_MAIN_2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 A B C G E H)
        (and (= G (+ (- 1) D)) (not (>= B A)) (>= E G) (= (+ H G) F))
      )
      (INV_MAIN_2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 H B C G E F)
        (and (= D 1) (not (>= B H)) (not (>= E G)) (= A 1))
      )
      (INV_MAIN_3 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_3 G B H I E J)
        (and (= (* 2 H) C)
     (= I (+ (- 1) D))
     (= G (+ (- 1) A))
     (>= B G)
     (>= E I)
     (= (* 2 J) F))
      )
      (INV_MAIN_3 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_3 G B H D E F)
        (and (= G (+ (- 1) A)) (>= B G) (not (>= E D)) (= (* 2 H) C))
      )
      (INV_MAIN_3 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_3 A B C G E H)
        (and (= G (+ (- 1) D)) (not (>= B A)) (>= E G) (= (* 2 H) F))
      )
      (INV_MAIN_3 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_3 F A B E C D)
        (and (not (>= A F)) (not (>= C E)))
      )
      (INV_MAIN_4 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_4 E F G H)
        (and (= (+ F E) B) (= G (+ 1 C)) (= E (+ 1 A)) (>= G 1) (>= E 0) (= (+ H G) D))
      )
      (INV_MAIN_4 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_4 E F C D)
        (and (= E (+ 1 A)) (>= E 0) (not (>= C 1)) (= (+ F E) B))
      )
      (INV_MAIN_4 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_4 A B E F)
        (and (= E (+ 1 C)) (>= E 1) (not (>= A 0)) (= (+ F E) D))
      )
      (INV_MAIN_4 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_4 D A C B)
        (and (not (>= D 0)) (not (>= C 1)) (not (= A B)))
      )
      false
    )
  )
)

(check-sat)
(exit)
