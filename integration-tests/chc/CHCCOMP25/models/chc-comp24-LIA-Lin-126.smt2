(set-logic HORN)


(declare-fun |g$unknown:3| ( Int Int Int ) Bool)
(declare-fun |twice$unknown:11| ( Int Int ) Bool)
(declare-fun |twice$unknown:13| ( Int Int ) Bool)
(declare-fun |neg$unknown:7| ( Int Int ) Bool)
(declare-fun |twice$unknown:15| ( Int Int ) Bool)
(declare-fun |twice$unknown:9| ( Int Int ) Bool)
(declare-fun |neg$unknown:5| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (= A B)
      )
      (|g$unknown:3| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|g$unknown:3| A C B)
        (and (not (= 0 E)) (= D 1) (not (= (= 0 E) (>= B 0))))
      )
      (|twice$unknown:13| A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|neg$unknown:5| D C)
        (and (= C 1) (= A (* (- 1) D)))
      )
      (|neg$unknown:7| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|twice$unknown:11| A B)
        true
      )
      (|twice$unknown:9| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|twice$unknown:11| C B)
        (= A C)
      )
      (|twice$unknown:15| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|twice$unknown:13| A B)
        true
      )
      (|twice$unknown:9| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|twice$unknown:9| B A)
        (and (not (= 0 E)) (= D 1) (not (= (= 0 E) (>= C 0))))
      )
      (|neg$unknown:5| B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|neg$unknown:7| B A)
        (and (not (= 0 E)) (= D 1) (not (= (= 0 E) (>= C 0))))
      )
      (|twice$unknown:11| B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|twice$unknown:15| D C)
        (and (not (= (= 0 E) (>= A 0)))
     (= 0 B)
     (not (= 0 E))
     (= C 1)
     (not (= (= 0 B) (>= D 0))))
      )
      false
    )
  )
)

(check-sat)
(exit)
