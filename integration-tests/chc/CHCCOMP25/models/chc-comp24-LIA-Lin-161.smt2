(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and (= A B) (= 0 v_2) (= 10 v_3))
      )
      (INV_MAIN_42 v_2 A v_3 B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 C A D B)
        (let ((a!1 (not (= C (+ 10 (* (- 1) D))))))
  (and a!1 (= C A) (= D (+ 10 (* (- 1) B)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 C A D B)
        (let ((a!1 (not (= C (+ 11 (* (- 1) D))))) (a!2 (not (= D (+ 10 (* (- 1) B))))))
  (and a!1 (= C A) (not (>= D 1)) a!2))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 C A D B)
        (let ((a!1 (not (= C (+ 9 (* (- 1) D))))))
  (and a!1 (not (= C A)) (not (<= C 9)) (= D (+ 10 (* (- 1) B)))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 C A D B)
        (let ((a!1 (not (= C (+ 10 (* (- 1) D))))) (a!2 (not (= D (+ 10 (* (- 1) B))))))
  (and a!1 (not (= C A)) (not (>= D 1)) (not (<= C 9)) a!2))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F)
        (let ((a!1 (not (= E (+ 10 (* (- 1) F))))))
  (and (= A (+ (- 1) E)) a!1 (= B (+ 1 C)) (>= E 1) (<= C 9) (not (= C D))))
      )
      (INV_MAIN_42 B D A F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (INV_MAIN_42 B C D E)
        (let ((a!1 (or (not (>= D 1)) (= D (+ 10 (* (- 1) E))))))
  (and (= A (+ 1 B)) (<= B 9) a!1 (not (= B C))))
      )
      (INV_MAIN_42 A C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (INV_MAIN_42 B C D E)
        (let ((a!1 (not (= D (+ 10 (* (- 1) E))))))
  (and (= A (+ (- 1) D)) (>= D 1) (or (not (<= B 9)) (= B C)) a!1))
      )
      (INV_MAIN_42 B C A E)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        END_QUERY
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
