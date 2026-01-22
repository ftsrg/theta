(set-logic HORN)


(declare-fun |INV_MAIN_23| ( Int Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_13| ( Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (and (= F D) (= E 0) (= A C) (not (>= F 1)) (= G B))
      )
      (INV_MAIN_23 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (and (= H F) (= G 0) (= C 0) (= B E) (>= H 1) (= A D))
      )
      (INV_MAIN_42 A B C D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_13 E F G H)
        (and (= G (+ 1 C))
     (= F (+ (- 2) B))
     (= E (+ 1 A))
     (>= G 1)
     (>= E 1)
     (= H (+ (- 2) D)))
      )
      (INV_MAIN_13 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_13 E F C D)
        (and (= E (+ 1 A)) (>= E 1) (not (>= C 1)) (= F (+ (- 2) B)))
      )
      (INV_MAIN_13 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_13 A B E F)
        (and (= E (+ 1 C)) (>= E 1) (not (>= A 1)) (= F (+ (- 2) D)))
      )
      (INV_MAIN_13 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_23 A E C F D)
        (and (not (>= E 1)) (= B 0))
      )
      (INV_MAIN_13 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (INV_MAIN_23 A F C D G)
        (and (= F (+ 1 B)) (>= F 1) (>= D 1) (= G (+ (- 1) E)))
      )
      (INV_MAIN_23 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_23 A F C D E)
        (and (>= F 1) (not (>= D 1)) (= F (+ 1 B)))
      )
      (INV_MAIN_23 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (INV_MAIN_42 F A B E C G D)
        (and (not (>= E 1)) (not (>= F 1)))
      )
      (INV_MAIN_13 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_42 H B I J E F G)
        (and (= I (+ (- 1) C))
     (= H (+ 1 A))
     (>= J 1)
     (>= H 1)
     (not (>= F 1))
     (= J (+ 1 D)))
      )
      (INV_MAIN_42 A B C D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (INV_MAIN_42 H B I J E F K)
        (and (= J (+ 1 D))
     (= I (+ (- 1) C))
     (= H (+ 1 A))
     (>= J 1)
     (>= H 1)
     (>= F 1)
     (= K (+ (- 1) G)))
      )
      (INV_MAIN_42 A B C D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 H B I D E F G)
        (and (= H (+ 1 A)) (>= H 1) (not (>= D 1)) (= I (+ (- 1) C)))
      )
      (INV_MAIN_42 A B C D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C H E F G)
        (and (not (>= A 1)) (>= H 1) (not (>= F 1)) (= H (+ 1 D)))
      )
      (INV_MAIN_42 A B C D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C H E F I)
        (and (= H (+ 1 D)) (not (>= A 1)) (>= H 1) (>= F 1) (= I (+ (- 1) G)))
      )
      (INV_MAIN_42 A B C D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_13 D A C B)
        (and (not (>= D 1)) (not (>= C 1)) (not (= A B)))
      )
      false
    )
  )
)

(check-sat)
(exit)
