(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_23| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (= C F) (= B 0) (= A D) (= E 0))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_23 A G H D I J)
        (and (= I (+ (- 2) E))
     (= H (+ (- 1) C))
     (= G (+ (- 1) B))
     (>= (+ D (* (- 1) J)) 1)
     (>= (+ A (* (- 1) H)) 1)
     (= J (+ (- 1) F)))
      )
      (INV_MAIN_23 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_23 A G H D E F)
        (let ((a!1 (not (>= (+ D (* (- 1) F)) 1))))
  (and (= G (+ (- 1) B)) (>= (+ A (* (- 1) H)) 1) a!1 (= H (+ (- 1) C))))
      )
      (INV_MAIN_23 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_23 A B C D G H)
        (let ((a!1 (not (>= (+ A (* (- 1) C)) 1))))
  (and (= G (+ (- 2) E)) a!1 (>= (+ D (* (- 1) H)) 1) (= H (+ (- 1) F))))
      )
      (INV_MAIN_23 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (INV_MAIN_23 B G C E D F)
        (let ((a!1 (not (>= (+ E (* (- 1) F)) 1))) (a!2 (not (>= (+ B (* (- 1) C)) 1))))
  (and a!1 a!2 (= G (+ (- 1) A))))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_42 H G C J I F)
        (and (= I (+ (- 1) D))
     (= H (+ 2 B))
     (= G (+ (- 1) A))
     (>= (+ C (* (- 1) G)) 1)
     (>= (+ F (* (- 1) I)) 1)
     (= J (+ 2 E)))
      )
      (INV_MAIN_23 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 E D C F B A)
        (let ((a!1 (not (>= (+ C (* (- 1) D)) 1))))
  (and (>= (+ A (* (- 1) B)) 1) a!1))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 E D C F B A)
        (let ((a!1 (not (>= (+ A (* (- 1) B)) 1))))
  (and a!1 (>= (+ C (* (- 1) D)) 1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 A F E B D C)
        (let ((a!1 (not (>= (+ E (* (- 1) F)) 1))) (a!2 (not (>= (+ C (* (- 1) D)) 1))))
  (and a!1 a!2 (not (= A B))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
