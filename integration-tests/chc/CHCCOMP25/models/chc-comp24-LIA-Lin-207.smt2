(set-logic HORN)


(declare-fun |REC_f_| ( Int Int ) Bool)
(declare-fun |REC__f| ( Int Int Int ) Bool)
(declare-fun |REC_f_f| ( Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC__f F G E)
        (and (= B 0)
     (= C (+ 1 F))
     (>= (+ C D) 16)
     (<= A 0)
     (not (<= C 0))
     (= (+ C D) (+ 32 G)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC__f F G E)
        (let ((a!1 (not (>= (+ (* (- 1) C) (* (- 1) D)) 17))))
  (and (= B 0)
       (= C (+ 1 F))
       a!1
       (not (>= (+ C D) 16))
       (<= A 0)
       (not (<= C 0))
       (= (+ C D) G)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC__f F G E)
        (and (= B 0)
     (= C (+ 1 F))
     (>= (+ (* (- 1) C) (* (- 1) D)) 17)
     (not (>= (+ C D) 16))
     (<= A 0)
     (not (<= C 0))
     (= (+ C D) (+ (- 32) G)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) ) 
    (=>
      (and
        (and (<= C 0) (<= A 0) (= B 0) (= v_4 D))
      )
      (REC_f_f A B C D v_4)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (and (= (+ F A) (+ 32 B))
     (= A (+ 1 G))
     (= C (+ 1 H))
     (>= (+ C D) 16)
     (>= (+ F A) 16)
     (not (<= A 0))
     (not (<= C 0))
     (= (+ C D) (+ 32 I)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (let ((a!1 (not (>= (+ (* (- 1) F) (* (- 1) A)) 17))))
  (and (= (+ F A) B)
       (= A (+ 1 G))
       (= C (+ 1 H))
       a!1
       (>= (+ C D) 16)
       (not (>= (+ F A) 16))
       (not (<= A 0))
       (not (<= C 0))
       (= (+ C D) (+ 32 I))))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (and (= (+ F A) (+ (- 32) B))
     (= A (+ 1 G))
     (= C (+ 1 H))
     (>= (+ (* (- 1) F) (* (- 1) A)) 17)
     (>= (+ C D) 16)
     (not (>= (+ F A) 16))
     (not (<= A 0))
     (not (<= C 0))
     (= (+ C D) (+ 32 I)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (let ((a!1 (not (>= (+ (* (- 1) C) (* (- 1) D)) 17))))
  (and (= (+ F A) (+ (- 32) B))
       (= A (+ 1 G))
       (= C (+ 1 H))
       a!1
       (>= (+ (* (- 1) F) (* (- 1) A)) 17)
       (not (>= (+ C D) 16))
       (not (>= (+ F A) 16))
       (not (<= A 0))
       (not (<= C 0))
       (= (+ C D) I)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (let ((a!1 (not (>= (+ (* (- 1) C) (* (- 1) D)) 17)))
      (a!2 (not (>= (+ (* (- 1) F) (* (- 1) A)) 17))))
  (and (= (+ F A) B)
       (= A (+ 1 G))
       (= C (+ 1 H))
       a!1
       a!2
       (not (>= (+ C D) 16))
       (not (>= (+ F A) 16))
       (not (<= A 0))
       (not (<= C 0))
       (= (+ C D) I)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (let ((a!1 (not (>= (+ (* (- 1) C) (* (- 1) D)) 17))))
  (and (= (+ F A) (+ 32 B))
       (= A (+ 1 G))
       (= C (+ 1 H))
       a!1
       (not (>= (+ C D) 16))
       (>= (+ F A) 16)
       (not (<= A 0))
       (not (<= C 0))
       (= (+ C D) I)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (and (= (+ F A) (+ (- 32) B))
     (= A (+ 1 G))
     (= C (+ 1 H))
     (>= (+ (* (- 1) C) (* (- 1) D)) 17)
     (>= (+ (* (- 1) F) (* (- 1) A)) 17)
     (not (>= (+ C D) 16))
     (not (>= (+ F A) 16))
     (not (<= A 0))
     (not (<= C 0))
     (= (+ C D) (+ (- 32) I)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (let ((a!1 (not (>= (+ (* (- 1) F) (* (- 1) A)) 17))))
  (and (= (+ F A) B)
       (= A (+ 1 G))
       (= C (+ 1 H))
       (>= (+ (* (- 1) C) (* (- 1) D)) 17)
       a!1
       (not (>= (+ C D) 16))
       (not (>= (+ F A) 16))
       (not (<= A 0))
       (not (<= C 0))
       (= (+ C D) (+ (- 32) I))))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (REC_f_f G F H I E)
        (and (= (+ F A) (+ 32 B))
     (= A (+ 1 G))
     (= C (+ 1 H))
     (>= (+ (* (- 1) C) (* (- 1) D)) 17)
     (not (>= (+ C D) 16))
     (>= (+ F A) 16)
     (not (<= A 0))
     (not (<= C 0))
     (= (+ C D) (+ (- 32) I)))
      )
      (REC_f_f A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) ) 
    (=>
      (and
        (REC_f_ F E)
        (and (= A (+ 1 F))
     (>= (+ (* (- 1) E) (* (- 1) A)) 17)
     (not (>= (+ E A) 16))
     (not (<= A 0))
     (<= C 0)
     (= (+ E A) (+ (- 32) B))
     (= v_6 D))
      )
      (REC_f_f A B C D v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) ) 
    (=>
      (and
        (REC_f_ F E)
        (let ((a!1 (not (>= (+ (* (- 1) E) (* (- 1) A)) 17))))
  (and (= A (+ 1 F))
       a!1
       (not (>= (+ E A) 16))
       (not (<= A 0))
       (<= C 0)
       (= (+ E A) B)
       (= v_6 D)))
      )
      (REC_f_f A B C D v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) ) 
    (=>
      (and
        (REC_f_ F E)
        (and (= A (+ 1 F))
     (>= (+ E A) 16)
     (not (<= A 0))
     (<= C 0)
     (= (+ E A) (+ 32 B))
     (= v_6 D))
      )
      (REC_f_f A B C D v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (<= A 0) (= B 0))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D C)
        (and (= A (+ 1 D)) (>= (+ C A) 16) (not (<= A 0)) (= (+ C A) (+ 32 B)))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D C)
        (let ((a!1 (not (>= (+ (* (- 1) C) (* (- 1) A)) 17))))
  (and (= A (+ 1 D)) a!1 (not (>= (+ C A) 16)) (not (<= A 0)) (= (+ C A) B)))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D C)
        (and (= A (+ 1 D))
     (>= (+ (* (- 1) C) (* (- 1) A)) 17)
     (not (>= (+ C A) 16))
     (not (<= A 0))
     (= (+ C A) (+ (- 32) B)))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) ) 
    (=>
      (and
        (and (<= A 0) (= v_2 B))
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
        (and (= A (+ 1 D))
     (>= (+ (* (- 1) A) (* (- 1) B)) 17)
     (not (>= (+ A B) 16))
     (not (<= A 0))
     (= (+ A B) (+ (- 32) E)))
      )
      (REC__f A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (REC__f D E C)
        (let ((a!1 (not (>= (+ (* (- 1) A) (* (- 1) B)) 17))))
  (and (= A (+ 1 D)) a!1 (not (>= (+ A B) 16)) (not (<= A 0)) (= (+ A B) E)))
      )
      (REC__f A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (REC__f D E C)
        (and (= A (+ 1 D)) (>= (+ A B) 16) (not (<= A 0)) (= (+ A B) (+ 32 E)))
      )
      (REC__f A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (REC_f_f D A E C B)
        (and (= C 0) (not (= A B)) (= D E))
      )
      false
    )
  )
)

(check-sat)
(exit)
