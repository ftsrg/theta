(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (and (= D H) (= A F) (= C B) (not D) (not A) (not C) (not (= (and F H) E)))
      )
      (state D C A H B F E G)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) ) 
    (=>
      (and
        (state D C A P B M L N)
        (let ((a!1 (= E (or (and B (not M)) (and (not B) M (not P)))))
      (a!2 (= G (or (and B M) (and (not M) P)))))
  (and (not (= (and J I) H))
       a!1
       (not (= M F))
       a!2
       (= I F)
       (= J G)
       (= K E)
       (= D P)
       (= C B)
       (= A M)
       (not (= (and M P) L))))
      )
      (state G E F J K I H O)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (state D C A H B F E G)
        (not E)
      )
      false
    )
  )
)

(check-sat)
(exit)
