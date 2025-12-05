(set-logic HORN)


(declare-fun |INV1| ( Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV1 A B C D E L K H I J)
        (and (= K (+ (- 2) F)) (= I J) (<= K 9) (not (<= B 9)) (= (* 2 K) (+ (- 4) G)))
      )
      (INV1 A B C D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (INV1 A K M D E N L H I J)
        (and (= (* 2 K) (+ (- 4) B))
     (= L (+ (- 2) F))
     (= K (+ (- 2) C))
     (= I J)
     (<= L 9)
     (<= K 9)
     (= (* 2 L) (+ (- 4) G)))
      )
      (INV1 A B C D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (INV1 A K L D E F G H I J)
        (and (= K (+ (- 2) C)) (= I J) (<= K 9) (not (<= G 9)) (= (* 2 K) (+ (- 4) B)))
      )
      (INV1 A B C D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (and (= F 0) (= C 0) (= B 1) (= A E) (= G 1) (= v_8 A) (= v_9 E))
      )
      (INV1 A B C D E F G H v_8 v_9)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV1 C A D E F G B H I J)
        (let ((a!1 (not (= (+ (* 2 A) (* (- 2) B)) 0))))
  (and (= I J) (not (<= B 9)) (not (<= A 9)) a!1))
      )
      false
    )
  )
)

(check-sat)
(exit)
