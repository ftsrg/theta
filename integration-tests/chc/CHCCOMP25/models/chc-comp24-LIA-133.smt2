(set-logic HORN)


(declare-fun |lock$unknown:8| ( Int Int ) Bool)
(declare-fun |unlock$unknown:10| ( Int Int ) Bool)
(declare-fun |f$unknown:2| ( Int Int ) Bool)
(declare-fun |lock$unknown:7| ( Int ) Bool)
(declare-fun |g$unknown:6| ( Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |unlock$unknown:9| ( Int ) Bool)
(declare-fun |f$unknown:3| ( Int Int Int ) Bool)
(declare-fun |g$unknown:5| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (= B 0)
      )
      (|f$unknown:2| B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|f$unknown:2| C B)
        (|lock$unknown:8| E C)
        (and (not (= 0 D)) (= A E) (= (= 0 D) (<= B 0)))
      )
      (|f$unknown:3| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|f$unknown:2| B A)
        (and (not (= 0 C)) (= (= 0 C) (<= A 0)))
      )
      (|lock$unknown:7| B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|f$unknown:2| C B)
        (and (= 0 D) (= A C) (= (= 0 D) (<= B 0)))
      )
      (|f$unknown:3| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|f$unknown:3| B C A)
        (= C 0)
      )
      (|g$unknown:5| B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|g$unknown:5| C B)
        (|unlock$unknown:10| E C)
        (and (not (= 0 D)) (= A E) (= (= 0 D) (<= B 0)))
      )
      (|g$unknown:6| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|g$unknown:5| B A)
        (and (not (= 0 C)) (= (= 0 C) (<= A 0)))
      )
      (|unlock$unknown:9| B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|g$unknown:5| C B)
        (and (= 0 D) (= A C) (= (= 0 D) (<= B 0)))
      )
      (|g$unknown:6| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|lock$unknown:7| B)
        (and (not (= 0 D)) (= A 1) (= C 1) (not (= (= 0 D) (= B 0))))
      )
      (|lock$unknown:8| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|unlock$unknown:9| B)
        (and (not (= 0 D)) (= A 0) (= C 1) (not (= (= 0 D) (= B 1))))
      )
      (|unlock$unknown:10| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|g$unknown:6| C B A)
        (|f$unknown:3| B E A)
        (and (= 0 D) (= E 0) (not (= (= 0 D) (= C 0))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|lock$unknown:7| A)
        (and (= 0 B) (not (= (= 0 B) (= A 0))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (|unlock$unknown:9| A)
        (and (= 0 B) (not (= (= 0 B) (= A 1))))
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
