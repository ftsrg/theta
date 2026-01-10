(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (= D 1) (= C (+ 1 F)) (= B 1) (= A 0) (= E 1))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_42 G H I J K L)
        (and (= (+ J K) D)
     (= (+ G H) B)
     (= (+ G H) A)
     (= L (+ 1 F))
     (= I (+ 1 C))
     (>= L 1)
     (>= I 1)
     (= (+ J K) E))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 G H I D E F)
        (and (= (+ G H) A) (= I (+ 1 C)) (>= I 1) (not (>= F 1)) (= (+ G H) B))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C G H I)
        (and (= (+ G H) D) (= I (+ 1 F)) (not (>= C 1)) (>= I 1) (= (+ G H) E))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 E A D F B C)
        (and (not (>= D 1)) (not (>= C 1)) (not (= A B)))
      )
      false
    )
  )
)

(check-sat)
(exit)
