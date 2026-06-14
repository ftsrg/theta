(set-logic HORN)


(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select J G) H))
     (not (= (select F C) D))
     (= A (+ 1 G))
     (= B (+ (- 1) E))
     (not (= I 0))
     (not (= E 0))
     (= E I)
     (= D H)
     (= C G)
     (= F J))
      )
      (INV_MAIN_42 D B C F H A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 E F G H I J K L)
        (let ((a!1 (not (= (select H (+ 1 G)) E))))
  (and a!1
       (= A (+ (- 1) K))
       (= B (+ 1 J))
       (= C (+ 1 G))
       (= D (+ (- 1) F))
       (not (= K 1))
       (not (= F 0))
       (not (= (select L J) I))))
      )
      (INV_MAIN_42 E D C H I B A L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (not (= (select F (+ 1 E)) C))))
  (and (= A (+ 1 E))
       (= B (+ (- 1) D))
       (not (= D 0))
       (or (= I 1) (= (select J H) G))
       a!1))
      )
      (INV_MAIN_42 C B A F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (or (= D 0) (= (select F (+ 1 E)) C))))
  (and (= A (+ (- 1) I))
       (= B (+ 1 H))
       (not (= I 1))
       a!1
       (not (= (select J H) G))))
      )
      (INV_MAIN_42 C D E F G B A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select H E) F))
     (= (select D A) B)
     (not (= G 0))
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select H E) F))
     (not (= G 0))
     (= C 0)
     (= C G)
     (= B F)
     (= A E)
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select H E) F)
     (not (= (select D A) B))
     (not (= G 0))
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (not (= (select D A) B))
     (= G 0)
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select H E) F)
     (= (select D A) B)
     (not (= G 0))
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (or (not (= A E)) (not (= D H)))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select D A) B)
     (= G 0)
     (not (= C 0))
     (= C G)
     (= B F)
     (= A E)
     (or (not (= A 0)) (not (= D H)))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select H E) F)
     (not (= G 0))
     (= C 0)
     (= C G)
     (= B F)
     (= A E)
     (or (not (= D H)) (not (= 0 E)))
     (= D H))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (let ((a!1 (or (not (= D H)) (not (= C (+ (- 1) F))))))
  (and (= (select D (+ 1 C)) A)
       (not (= G 1))
       (not (= B 0))
       a!1
       (= (select H F) E)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (and (= G 1)
     (not (= B 0))
     (or (not (= D H)) (not (= C (- 1))))
     (= (select D (+ 1 C)) A))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (and (not (= G 1)) (= B 0) (or (not (= D H)) (not (= 0 F))) (= (select H F) E))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F G H)
        (and (= G 1) (= B 0) (not (= D H)))
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
