; ./prepared/synth/nay-horn/./CONST_sum_2_15_000.smt2
(set-logic HORN)


(declare-fun |Start| ( Int Int ) Bool)
(declare-fun |StartBool| ( Bool Bool ) Bool)

(assert
  (forall ( (v_0 Int) (v_1 Int) ) 
    (=>
      (and
        (and true (= 0 v_0) (= 16 v_1))
      )
      (Start v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 Int) (v_1 Int) ) 
    (=>
      (and
        (and true (= 0 v_0) (= 0 v_1))
      )
      (Start v_0 v_1)
    )
  )
)
(assert
  (forall ( (v_0 Int) (v_1 Int) ) 
    (=>
      (and
        (and true (= 2 v_0) (= 2 v_1))
      )
      (Start v_0 v_1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (Start E F)
        (Start C D)
        (and (= B (+ C E)) (= A (+ D F)))
      )
      (Start B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (Start G H)
        (StartBool C D)
        (Start E F)
        (and (= B (ite C E G)) (= A (ite D F H)))
      )
      (Start B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) ) 
    (=>
      (and
        (StartBool C D)
        (and (not (= C B)) (not (= D A)))
      )
      (StartBool B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) ) 
    (=>
      (and
        (StartBool C D)
        (and (= A D) (= B C))
      )
      (StartBool B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (Start E F)
        (Start C D)
        (and (= A (>= D F)) (= B (>= C E)))
      )
      (StartBool B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) ) 
    (=>
      (and
        (StartBool E F)
        (StartBool C D)
        (and (= A (and F D)) (= B (and E C)))
      )
      (StartBool B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (Start A B)
        (and (= A 0) (= B 17))
      )
      false
    )
  )
)

(check-sat)
(exit)
