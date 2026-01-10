(set-logic HORN)


(declare-fun |REC__f| ( Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |REC_f_| ( Int Int Int ) Bool)
(declare-fun |REC_f_f| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (and (not (= C 0)) (= C 1) (= A 0) (= D (+ (- 1) E)) (= v_5 B))
      )
      (REC_f_f A B v_5 C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (v_7 Int) ) 
    (=>
      (and
        (REC__f F G E)
        (and (not (= C 2))
     (not (= C 0))
     (not (= C 1))
     (= C (+ 1 F))
     (= A 0)
     (= D (+ (- 1) G))
     (= v_7 B))
      )
      (REC_f_f A B v_7 C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (not (= C 0)) (not (= C 1)) (= A 0) (= C 2) (= v_4 B) (= v_5 D))
      )
      (REC_f_f A B v_4 C D v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (= A 0) (= C 0) (= v_4 B) (= v_5 D))
      )
      (REC_f_f A B v_4 C D v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (REC_f_ G H C)
        (and (= A (+ 1 G))
     (= E (+ (- 1) F))
     (not (= D 0))
     (= D 1)
     (= B (+ (- 1) H))
     (not (= A 0)))
      )
      (REC_f_f A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (REC_f_f G H C I J F)
        (and (not (= A 0))
     (= A (+ 1 G))
     (= E (+ (- 1) J))
     (not (= D 2))
     (not (= D 0))
     (not (= D 1))
     (= D (+ 1 I))
     (= B (+ (- 1) H)))
      )
      (REC_f_f A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (v_7 Int) ) 
    (=>
      (and
        (REC_f_ F G C)
        (and (not (= D 0))
     (not (= D 1))
     (= B (+ (- 1) G))
     (not (= A 0))
     (= A (+ 1 F))
     (= D 2)
     (= v_7 E))
      )
      (REC_f_f A B C D E v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (v_7 Int) ) 
    (=>
      (and
        (REC_f_ F G C)
        (and (= B (+ (- 1) G)) (not (= A 0)) (= A (+ 1 F)) (= D 0) (= v_7 E))
      )
      (REC_f_f A B C D E v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) ) 
    (=>
      (and
        (and (= A 0) (= v_2 B))
      )
      (REC_f_ A B v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (REC_f_ D E C)
        (and (not (= A 0)) (= A (+ 1 D)) (= B (+ (- 1) E)))
      )
      (REC_f_ A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) ) 
    (=>
      (and
        (and (= A 0) (= v_2 B))
      )
      (REC__f A B v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) ) 
    (=>
      (and
        (and (not (= A 0)) (not (= A 1)) (= A 2) (= v_2 B))
      )
      (REC__f A B v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (REC__f D E C)
        (and (not (= A 2)) (not (= A 0)) (not (= A 1)) (= A (+ 1 D)) (= B (+ (- 1) E)))
      )
      (REC__f A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (not (= A 0)) (= A 1) (= B (+ (- 1) C)))
      )
      (REC__f A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC_f_ D F A)
        (and (= E (+ (- 1) F))
     (= E B)
     (not (= C 0))
     (= C (+ 1 D))
     (= C G)
     (not (= A B))
     (= G 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC_f_ D F A)
        (and (not (= G 0))
     (not (= G 1))
     (= E (+ (- 1) F))
     (= E B)
     (not (= C 0))
     (= C (+ 1 D))
     (= C G)
     (not (= A B))
     (= G 2))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (REC_f_f D F A H J B)
        (and (= C (+ 1 D))
     (= C G)
     (not (= A B))
     (= I (+ (- 1) J))
     (not (= G 2))
     (not (= G 0))
     (not (= G 1))
     (= G (+ 1 H))
     (= E (+ (- 1) F))
     (= E I)
     (not (= C 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC_f_ D F A)
        (and (= G 1)
     (= E (+ (- 1) F))
     (= E B)
     (not (= C 0))
     (= C (+ 1 D))
     (= C G)
     (not (= A (+ 1 B)))
     (not (= G 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC__f D F B)
        (and (= G C)
     (= E (+ (- 1) F))
     (not (= C 2))
     (not (= C 0))
     (not (= C 1))
     (= C (+ 1 D))
     (= A E)
     (not (= A B))
     (= G 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= D C) (not (= C 0)) (= C 1) (not (= A (+ 1 B))) (= A B) (= D 0))
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
