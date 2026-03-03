(set-logic HORN)


(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select K H) (* (- 1) (select K I))) 0)))
  (and (not (= (select K H) 0))
       (= (select G D) (select G E))
       (not (= (select G D) 0))
       (not (= 0 J))
       a!1
       (= A (+ H J))
       (= B (+ 1 D))
       (= C (+ 1 E))
       (not (= F 0))
       (= F J)
       (= E I)
       (= D H)
       (= G K)))
      )
      (INV_MAIN_42 C B F G H A I K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F G H I J K L M)
        (let ((a!1 (+ (select M (+ 1 J)) (* (- 1) (select M (+ 1 L)))))
      (a!2 (not (= (select M (+ 1 J)) 0))))
  (and (= (select I G) (select I F))
       (not (= (select I G) 0))
       (= a!1 0)
       (= A (+ 1 L))
       (= B (+ 1 J))
       (= C (+ (- 1) H))
       (= D (+ 1 G))
       (= E (+ 1 F))
       (not (= J (+ (- 1) K)))
       (not (= H 1))
       a!2))
      )
      (INV_MAIN_42 E D C I B K A M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I J K)
        (let ((a!1 (+ (select K (+ 1 H)) (* (- 1) (select K (+ 1 J))))))
(let ((a!2 (or (not (= a!1 0)) (= H (+ (- 1) I)) (= (select K (+ 1 H)) 0))))
  (and (not (= (select G E) 0))
       (= A (+ (- 1) F))
       (= B (+ 1 E))
       (= C (+ 1 D))
       (not (= F 1))
       a!2
       (= (select G E) (select G D)))))
      )
      (INV_MAIN_42 C B A G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H I J)
        (let ((a!1 (+ (select J (+ 1 G)) (* (- 1) (select J (+ 1 I)))))
      (a!2 (or (= (select F D) 0) (not (= (select F D) (select F C))) (= E 1)))
      (a!3 (not (= (select J (+ 1 G)) 0))))
  (and (= a!1 0) (= A (+ 1 I)) (= B (+ 1 G)) (not (= G (+ (- 1) H))) a!2 a!3))
      )
      (INV_MAIN_42 C D E F B H A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0)))
  (and (not (= (select H E) 0))
       (not (= 0 G))
       a!1
       (= C 0)
       (= C G)
       (= B F)
       (= A E)
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0)))
  (and (not (= (select H E) 0))
       (not (= (select D A) (select D B)))
       (not (= 0 G))
       a!1
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0)))
  (and (not (= (select H E) 0))
       (= (select D A) (select D B))
       (= (select D A) 0)
       (not (= 0 G))
       a!1
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0)))
  (and (= (select D A) (select D B))
       (not (= (select D A) 0))
       (not (= 0 G))
       (not a!1)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0)))
  (and (= (select H E) 0)
       (= (select D A) (select D B))
       (not (= (select D A) 0))
       (not (= 0 G))
       a!1
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (and (= (select D A) (select D B))
     (not (= (select D A) 0))
     (= 0 G)
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
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= 0 G))
       (not a!1)
       (= C 0)
       (= C G)
       (= B F)
       (= A E)
       (or (not a!2) (not (= D H)))
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0))
      (a!2 (= (+ (select D A) (* (- 1) (select D B)))
              (+ (select H E) (* (- 1) (select H F))))))
  (and (not (= (select D A) (select D B)))
       (not (= 0 G))
       (not a!1)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (or (not (= D H)) (not a!2))
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0))
      (a!2 (= (+ (select D A) (* (- 1) (select D B))) 0)))
  (and (= (select H E) 0)
       (not (= (select D A) (select D B)))
       (not (= 0 G))
       a!1
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (or (not (= D H)) (not a!2))
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select D A) (* (- 1) (select D B))) 0)))
  (and (not (= (select D A) (select D B)))
       (= 0 G)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (or (not (= D H)) (not a!1))
       (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (let ((a!1 (= (+ (select H E) (* (- 1) (select H F))) 0))
      (a!2 (= 0 (+ (select H E) (* (- 1) (select H F))))))
  (and (= (select D A) (select D B))
       (= (select D A) 0)
       (not (= 0 G))
       (not a!1)
       (not (= C 0))
       (= C G)
       (= B F)
       (= A E)
       (or (not a!2) (not (= D H)))
       (= D H)))
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
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 G))))))
(let ((a!2 (= (+ (select D B) (* (- 1) (select D A))) a!1)))
  (and (not (= a!1 0))
       (not (= E (+ (- 1) F)))
       (not (= C 1))
       (or (not (= D H)) (not a!2))
       (not (= (select D B) (select D A))))))
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
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 G)))))
      (a!2 (= (+ (select D B) (* (- 1) (select D A))) 0)))
  (and (not (= (select D B) (select D A)))
       (= a!1 0)
       (not (= E (+ (- 1) F)))
       (not (= C 1))
       (or (not (= D H)) (not a!2))
       (= (select H (+ 1 E)) 0)))
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
        (let ((a!1 (= (+ (select D B) (* (- 1) (select D A))) 0)))
  (and (= E (+ (- 1) F))
       (not (= C 1))
       (or (not (= D H)) (not a!1))
       (not (= (select D B) (select D A)))))
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
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 G))))))
  (and (= (select D B) 0)
       (not (= a!1 0))
       (not (= E (+ (- 1) F)))
       (not (= C 1))
       (or (not (= D H)) (not (= 0 a!1)))
       (= (select D B) (select D A))))
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
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 G))))))
  (and (= (select H (+ 1 E)) 0)
       (= (select D B) (select D A))
       (= (select D B) 0)
       (= a!1 0)
       (not (= E (+ (- 1) F)))
       (not (= C 1))
       (not (= D H))))
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
        (and (= (select D B) (select D A))
     (= (select D B) 0)
     (= E (+ (- 1) F))
     (not (= C 1))
     (not (= D H)))
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
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 G))))))
  (and (not (= E (+ (- 1) F)))
       (= C 1)
       (or (not (= D H)) (not (= 0 a!1)))
       (not (= a!1 0))))
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
        (let ((a!1 (+ (select H (+ 1 E)) (* (- 1) (select H (+ 1 G))))))
  (and (= (select H (+ 1 E)) 0)
       (= a!1 0)
       (not (= E (+ (- 1) F)))
       (= C 1)
       (not (= D H))))
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
        (and (= E (+ (- 1) F)) (= C 1) (not (= D H)))
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
