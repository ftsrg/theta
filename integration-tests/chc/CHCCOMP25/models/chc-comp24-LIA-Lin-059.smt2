(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (let ((a!1 (and (or (not H) (not A) (not F))
                (or A
                    (not H)
                    (not F)
                    (and (not A) F (not H))
                    (and (not A) (not F) H)
                    (and A F H)))))
  (and (= D A) (= B F) (= C H) (not D) (= B true) (not C) (= a!1 E)))
      )
      (state D C B A H F E G)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) ) 
    (=>
      (and
        (state D C B A P M L N)
        (let ((a!1 (and (or (not P) (not A) (not M))
                (or A
                    (not P)
                    (not M)
                    (and (not A) M (not P))
                    (and A M P)
                    (and (not A) (not M) P))))
      (a!2 (and (or (not K) (not J) (not I))
                (or K
                    (not J)
                    (not I)
                    (and K J I)
                    (and (not K) J (not I))
                    (and (not K) (not J) I)))))
  (and (= a!1 L)
       (= P G)
       (= M F)
       (= I E)
       (= J F)
       (= K G)
       (= D A)
       (= C P)
       (= B M)
       (= A E)
       (= a!2 H)))
      )
      (state G F E K J I H O)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (state D C B A H F E G)
        (not E)
      )
      false
    )
  )
)

(check-sat)
(exit)
