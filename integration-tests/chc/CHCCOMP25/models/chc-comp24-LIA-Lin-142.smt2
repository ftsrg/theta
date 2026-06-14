(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= B D) (= A 0) (= C 10))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 E B F D)
        (let ((a!1 (not (= F (+ 10 (* (- 1) D))))))
  (and (= F (+ 1 C)) (= E (+ (- 1) A)) (not (= E B)) (>= F 1) (<= E 9) a!1))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (INV_MAIN_42 E B C D)
        (let ((a!1 (or (not (>= C 1)) (= C (+ 10 (* (- 1) D))))))
  (and (not (= E B)) (<= E 9) a!1 (= E (+ (- 1) A))))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B E D)
        (let ((a!1 (not (= E (+ 10 (* (- 1) D))))))
  (and (= E (+ 1 C)) (>= E 1) (or (not (<= A 9)) (= A B)) a!1))
      )
      (INV_MAIN_42 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 A D B C)
        (let ((a!1 (not (= A (+ 10 (* (- 1) B))))))
  (and a!1 (= A D) (= B (+ 10 (* (- 1) C)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 A D B C)
        (let ((a!1 (not (= A (+ 11 (* (- 1) B))))) (a!2 (not (= B (+ 10 (* (- 1) C))))))
  (and a!1 (= A D) (not (>= B 1)) a!2))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 A D B C)
        (let ((a!1 (not (= A (+ 9 (* (- 1) B))))))
  (and a!1 (not (= A D)) (not (<= A 9)) (= B (+ 10 (* (- 1) C)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_42 A D B C)
        (let ((a!1 (not (= A (+ 10 (* (- 1) B))))) (a!2 (not (= B (+ 10 (* (- 1) C))))))
  (and a!1 (not (= A D)) (not (>= B 1)) (not (<= A 9)) a!2))
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
