(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)
(declare-fun |incr$unknown:6| ( Int Int ) Bool)
(declare-fun |f$unknown:4| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|f$unknown:2| A B)
        (and (not (= 0 D)) (= E (- 4)) (= (= 0 D) (<= (- 3) C)))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (|f$unknown:2| A B)
        (and (= (= 0 D) (<= (- 3) C))
     (= 0 E)
     (= 0 D)
     (= F (+ (- 2) C))
     (not (= (= 0 E) (<= C 1))))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (|f$unknown:4| A E)
        (and (not (= (= 0 D) (<= B 1)))
     (= 0 C)
     (= 0 D)
     (= F (+ (- 2) B))
     (= (= 0 C) (<= (- 3) B)))
      )
      (|f$unknown:2| A E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|incr$unknown:6| A C)
        (= B 3)
      )
      (|f$unknown:2| A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|f$unknown:2| E B)
        (and (= (= 0 C) (<= (- 3) B))
     (not (= 0 D))
     (= 0 C)
     (= A E)
     (not (= (= 0 D) (<= B 1))))
      )
      (|f$unknown:4| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|f$unknown:4| E D)
        (and (not (= 0 C)) (= A E) (= D (- 4)) (= (= 0 C) (<= (- 3) B)))
      )
      (|f$unknown:4| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (|f$unknown:4| F E)
        (and (not (= (= 0 D) (<= B 1)))
     (= 0 C)
     (= 0 D)
     (= A F)
     (= E (+ (- 2) B))
     (= (= 0 C) (<= (- 3) B)))
      )
      (|f$unknown:4| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (= A (+ 1 B))
      )
      (|incr$unknown:6| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|f$unknown:4| B A)
        (and (= 0 C) (= A 3) (not (= (= 0 C) (>= B (- 3)))))
      )
      false
    )
  )
)

(check-sat)
(exit)
