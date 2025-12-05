(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Int Bool Bool Bool Bool Int Bool Bool Bool Bool Bool Int ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Bool) (O Int) ) 
    (=>
      (and
        (and (= M L)
     (= (= L 5) J)
     (= (= I H) G)
     (= (and B A) K)
     (= C A)
     (= K I)
     (= J H)
     (= E D)
     (= F B)
     (not C)
     (not E)
     (not F)
     (= M 0))
      )
      (state F E C M B D A K L J I H G N O)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Int) (I Int) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Int) (B1 Int) (C1 Bool) (D1 Int) ) 
    (=>
      (and
        (state G F D B1 C E B Z A1 Y X W V C1 D1)
        (let ((a!1 (= K (or (and (not B) E) (and B (not C) (not E))))))
  (and (= I H)
       (= R I)
       (= (= A1 5) Y)
       (= (= R 5) P)
       (= (= X W) V)
       (= (= O N) M)
       (= (and T S) Q)
       (= (and B C) Z)
       (= Z X)
       (= Y W)
       a!1
       (= P N)
       (= Q O)
       (= S J)
       (= T L)
       (= G C)
       (= F E)
       (= D B)
       (not (= B J))
       (= U K)
       (or (= A1 5) (= A1 H))
       (or (= H 1) (not (= A1 5)))
       (not L)
       (= B1 A1)))
      )
      (state L K J I T U S Q R P O N M A H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Bool) (O Int) ) 
    (=>
      (and
        (state F E C M B D A K L J I H G N O)
        (not G)
      )
      false
    )
  )
)

(check-sat)
(exit)
