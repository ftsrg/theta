(set-logic HORN)


(declare-fun |INV_MAIN_2| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int Int Int Int ) Bool)

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
        (and (= (* 5 H) C)
     (= I (+ (- 1) D))
     (= G (+ (- 1) A))
     (>= B G)
     (>= E I)
     (= (* 5 J) F))
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
        (and (= G (+ (- 1) A)) (>= B G) (not (>= E D)) (= (* 5 H) C))
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
        (and (= G (+ (- 1) D)) (not (>= B A)) (>= E G) (= (* 5 H) F))
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
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_2 F E A D C B)
        (and (not (>= E F)) (not (>= C D)) (not (= A B)))
      )
      false
    )
  )
)

(check-sat)
(exit)
