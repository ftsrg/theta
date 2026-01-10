(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (let ((a!1 (and (or (and (not A) F (not H)) (and A F H))
                (or (not H) (not A) (not F)))))
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
        (let ((a!1 (and (or (and (not A) M (not P)) (and A M P))
                (or (not P) (not A) (not M))))
      (a!2 (and (or (and K J I) (and (not K) (not J) I))
                (or (not K) (not J) (not I)))))
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
