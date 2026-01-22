(set-logic HORN)


(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F))
      )
      (INV_MAIN_42 B A C E D F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (let ((a!1 (not (= (select H (+ 2 G)) F)))
      (a!2 (not (= (select H (+ 1 G)) 0)))
      (a!3 (not (= (select H (+ 1 G)) F)))
      (a!4 (not (= (select E (+ 3 D)) 0)))
      (a!5 (not (= (select E (+ 3 D)) C)))
      (a!6 (not (= (select E (+ 2 D)) 0)))
      (a!7 (not (= (select E (+ 2 D)) C)))
      (a!8 (not (= (select E (+ 1 D)) 0)))
      (a!9 (not (= (select E (+ 1 D)) C)))
      (a!10 (not (= (select H (+ 2 G)) 0))))
  (and a!1
       a!2
       a!3
       (not (= (select H G) 0))
       (not (= (select H G) F))
       a!4
       a!5
       a!6
       a!7
       a!8
       a!9
       (not (= (select E D) 0))
       (not (= (select E D) C))
       (= A (+ 3 G))
       (= B (+ 3 D))
       a!10))
      )
      (INV_MAIN_42 C B E F A H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 B C D E F G)
        (let ((a!1 (not (= (select D (+ 3 C)) B)))
      (a!2 (not (= (select D (+ 2 C)) 0)))
      (a!3 (not (= (select D (+ 2 C)) B)))
      (a!4 (not (= (select D (+ 1 C)) 0)))
      (a!5 (not (= (select D (+ 1 C)) B)))
      (a!6 (or (= (select G F) E)
               (= (select G (+ 1 F)) 0)
               (= (select G (+ 1 F)) E)
               (= (select G F) 0)
               (= (select G (+ 2 F)) 0)
               (= (select G (+ 2 F)) E)))
      (a!7 (not (= (select D (+ 3 C)) 0))))
  (and a!1
       a!2
       a!3
       a!4
       a!5
       (not (= (select D C) 0))
       (not (= (select D C) B))
       (= A (+ 3 C))
       a!6
       a!7))
      )
      (INV_MAIN_42 B A D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 B C D E F G)
        (let ((a!1 (not (= (select G (+ 2 F)) E)))
      (a!2 (not (= (select G (+ 1 F)) 0)))
      (a!3 (not (= (select G (+ 1 F)) E)))
      (a!4 (or (= (select D C) B)
               (= (select D C) 0)
               (= (select D (+ 3 C)) 0)
               (= (select D (+ 3 C)) B)
               (= (select D (+ 2 C)) 0)
               (= (select D (+ 2 C)) B)
               (= (select D (+ 1 C)) 0)
               (= (select D (+ 1 C)) B)))
      (a!5 (not (= (select G (+ 2 F)) 0))))
  (and a!1
       a!2
       a!3
       (not (= (select G F) 0))
       (not (= (select G F) E))
       (= A (+ 3 F))
       a!4
       a!5))
      )
      (INV_MAIN_42 B C D E A G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (= (select C B) A) (or (not (= B E)) (not (= C F))) (= (select F E) D))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (or (not (= C F)) (not (= B (+ 1 E))))))
  (and (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C B) A)
       a!1
       (= (select F (+ 1 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0)))
      (a!2 (not (= (select F (+ 1 E)) D)))
      (a!3 (or (not (= C F)) (not (= B (+ 2 E))))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C B) A)
       a!3
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D))))
  (and a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C B) A)
       (or (not (= C F)) (not (= B 0)))
       (= (select F (+ 2 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D))))
  (and a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C B) A)
       (or (not (= C F)) (not (= B 0)))
       (= (select F (+ 1 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (not (= (select F E) D))
     (= (select C B) A)
     (or (not (= C F)) (not (= B 0)))
     (= (select F E) 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (= (select C B) 0)
     (not (= (select C B) A))
     (or (not (= C F)) (not (= 0 E)))
     (= (select F E) D))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (not (= (select F E) 0))
     (not (= (select F E) D))
     (= (select C B) 0)
     (not (= (select C B) A))
     (or (not (= C F)) (not (= (- 1) E)))
     (= (select F (+ 1 E)) D))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0))) (a!2 (not (= (select F (+ 1 E)) D))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C B) 0)
       (not (= (select C B) A))
       (or (not (= C F)) (not (= (- 2) E)))
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D))))
  (and (= (select F (+ 2 E)) 0)
       a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C B) 0)
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D))))
  (and (= (select F (+ 1 E)) 0)
       a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C B) 0)
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (= (select F E) 0)
     (not (= (select F E) D))
     (= (select C B) 0)
     (not (= (select C B) A))
     (not (= C F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (or (not (= C F)) (not (= B (+ (- 1) E))))))
  (and (= (select C (+ 1 B)) A)
       (not (= (select C B) 0))
       (not (= (select C B) A))
       a!1
       (= (select F E) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (not (= (select F E) 0))
     (not (= (select F E) D))
     (= (select C (+ 1 B)) A)
     (not (= (select C B) 0))
     (not (= (select C B) A))
     (or (not (= B E)) (not (= C F)))
     (= (select F (+ 1 E)) D))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0)))
      (a!2 (not (= (select F (+ 1 E)) D)))
      (a!3 (or (not (= C F)) (not (= B (+ 1 E))))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 1 B)) A)
       (not (= (select C B) 0))
       (not (= (select C B) A))
       a!3
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D))))
  (and a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 1 B)) A)
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 1))))
       (= (select F (+ 2 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D))))
  (and a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 1 B)) A)
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 1))))
       (= (select F (+ 1 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (and (not (= (select F E) D))
     (= (select C (+ 1 B)) A)
     (not (= (select C B) 0))
     (not (= (select C B) A))
     (or (not (= C F)) (not (= B (- 1))))
     (= (select F E) 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 1 B)) A))))
  (and (= (select C (+ 1 B)) 0)
       a!1
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= 0 E)))
       (= (select F E) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 1 B)) A))))
  (and (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 1 B)) 0)
       a!1
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= (- 1) E)))
       (= (select F (+ 1 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0)))
      (a!2 (not (= (select F (+ 1 E)) D)))
      (a!3 (not (= (select C (+ 1 B)) A))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 1 B)) 0)
       a!3
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= (- 2) E)))
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D)))
      (a!4 (not (= (select C (+ 1 B)) A))))
  (and (= (select F (+ 2 E)) 0)
       a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 1 B)) 0)
       a!4
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D))) (a!2 (not (= (select C (+ 1 B)) A))))
  (and (= (select F (+ 1 E)) 0)
       a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 1 B)) 0)
       a!2
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 1 B)) A))))
  (and (= (select F E) 0)
       (not (= (select F E) D))
       (= (select C (+ 1 B)) 0)
       a!1
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 1 B)) 0)))
      (a!2 (not (= (select C (+ 1 B)) A)))
      (a!3 (or (not (= C F)) (not (= B (+ (- 2) E))))))
  (and (= (select C (+ 2 B)) A)
       a!1
       a!2
       (not (= (select C B) 0))
       (not (= (select C B) A))
       a!3
       (= (select F E) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 1 B)) 0)))
      (a!2 (not (= (select C (+ 1 B)) A)))
      (a!3 (or (not (= C F)) (not (= B (+ (- 1) E))))))
  (and (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) A)
       a!1
       a!2
       (not (= (select C B) 0))
       (not (= (select C B) A))
       a!3
       (= (select F (+ 1 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0)))
      (a!2 (not (= (select F (+ 1 E)) D)))
      (a!3 (not (= (select C (+ 1 B)) 0)))
      (a!4 (not (= (select C (+ 1 B)) A))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) A)
       a!3
       a!4
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= B E)) (not (= C F)))
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D)))
      (a!4 (not (= (select C (+ 1 B)) 0)))
      (a!5 (not (= (select C (+ 1 B)) A))))
  (and a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) A)
       a!4
       a!5
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 2))))
       (= (select F (+ 2 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D)))
      (a!2 (not (= (select C (+ 1 B)) 0)))
      (a!3 (not (= (select C (+ 1 B)) A))))
  (and a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) A)
       a!2
       a!3
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 2))))
       (= (select F (+ 1 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 1 B)) 0))) (a!2 (not (= (select C (+ 1 B)) A))))
  (and (not (= (select F E) D))
       (= (select C (+ 2 B)) A)
       a!1
       a!2
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 2))))
       (= (select F E) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 2 B)) A)))
      (a!2 (not (= (select C (+ 1 B)) 0)))
      (a!3 (not (= (select C (+ 1 B)) A))))
  (and (= (select C (+ 2 B)) 0)
       a!1
       a!2
       a!3
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= 0 E)))
       (= (select F E) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 2 B)) A)))
      (a!2 (not (= (select C (+ 1 B)) 0)))
      (a!3 (not (= (select C (+ 1 B)) A))))
  (and (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) 0)
       a!1
       a!2
       a!3
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= (- 1) E)))
       (= (select F (+ 1 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0)))
      (a!2 (not (= (select F (+ 1 E)) D)))
      (a!3 (not (= (select C (+ 2 B)) A)))
      (a!4 (not (= (select C (+ 1 B)) 0)))
      (a!5 (not (= (select C (+ 1 B)) A))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) 0)
       a!3
       a!4
       a!5
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= (- 2) E)))
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D)))
      (a!4 (not (= (select C (+ 2 B)) A)))
      (a!5 (not (= (select C (+ 1 B)) 0)))
      (a!6 (not (= (select C (+ 1 B)) A))))
  (and (= (select F (+ 2 E)) 0)
       a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) 0)
       a!4
       a!5
       a!6
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D)))
      (a!2 (not (= (select C (+ 2 B)) A)))
      (a!3 (not (= (select C (+ 1 B)) 0)))
      (a!4 (not (= (select C (+ 1 B)) A))))
  (and (= (select F (+ 1 E)) 0)
       a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 2 B)) 0)
       a!2
       a!3
       a!4
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 2 B)) A)))
      (a!2 (not (= (select C (+ 1 B)) 0)))
      (a!3 (not (= (select C (+ 1 B)) A))))
  (and (= (select F E) 0)
       (not (= (select F E) D))
       (= (select C (+ 2 B)) 0)
       a!1
       a!2
       a!3
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 2 B)) 0)))
      (a!2 (not (= (select C (+ 2 B)) A)))
      (a!3 (not (= (select C (+ 1 B)) 0)))
      (a!4 (not (= (select C (+ 1 B)) A)))
      (a!5 (or (not (= C F)) (not (= B (+ (- 3) E))))))
  (and (= (select C (+ 3 B)) A)
       a!1
       a!2
       a!3
       a!4
       (not (= (select C B) 0))
       (not (= (select C B) A))
       a!5
       (= (select F E) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 2 B)) 0)))
      (a!2 (not (= (select C (+ 2 B)) A)))
      (a!3 (not (= (select C (+ 1 B)) 0)))
      (a!4 (not (= (select C (+ 1 B)) A)))
      (a!5 (or (not (= C F)) (not (= B (+ (- 2) E))))))
  (and (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) A)
       a!1
       a!2
       a!3
       a!4
       (not (= (select C B) 0))
       (not (= (select C B) A))
       a!5
       (= (select F (+ 1 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0)))
      (a!2 (not (= (select F (+ 1 E)) D)))
      (a!3 (not (= (select C (+ 2 B)) 0)))
      (a!4 (not (= (select C (+ 2 B)) A)))
      (a!5 (not (= (select C (+ 1 B)) 0)))
      (a!6 (not (= (select C (+ 1 B)) A)))
      (a!7 (or (not (= C F)) (not (= B (+ (- 1) E))))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) A)
       a!3
       a!4
       a!5
       a!6
       (not (= (select C B) 0))
       (not (= (select C B) A))
       a!7
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D)))
      (a!4 (not (= (select C (+ 2 B)) 0)))
      (a!5 (not (= (select C (+ 2 B)) A)))
      (a!6 (not (= (select C (+ 1 B)) 0)))
      (a!7 (not (= (select C (+ 1 B)) A))))
  (and a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) A)
       a!4
       a!5
       a!6
       a!7
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 3))))
       (= (select F (+ 2 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D)))
      (a!2 (not (= (select C (+ 2 B)) 0)))
      (a!3 (not (= (select C (+ 2 B)) A)))
      (a!4 (not (= (select C (+ 1 B)) 0)))
      (a!5 (not (= (select C (+ 1 B)) A))))
  (and a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) A)
       a!2
       a!3
       a!4
       a!5
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 3))))
       (= (select F (+ 1 E)) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 2 B)) 0)))
      (a!2 (not (= (select C (+ 2 B)) A)))
      (a!3 (not (= (select C (+ 1 B)) 0)))
      (a!4 (not (= (select C (+ 1 B)) A))))
  (and (not (= (select F E) D))
       (= (select C (+ 3 B)) A)
       a!1
       a!2
       a!3
       a!4
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= B (- 3))))
       (= (select F E) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 3 B)) A)))
      (a!2 (not (= (select C (+ 2 B)) 0)))
      (a!3 (not (= (select C (+ 2 B)) A)))
      (a!4 (not (= (select C (+ 1 B)) 0)))
      (a!5 (not (= (select C (+ 1 B)) A))))
  (and (= (select C (+ 3 B)) 0)
       a!1
       a!2
       a!3
       a!4
       a!5
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= 0 E)))
       (= (select F E) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 3 B)) A)))
      (a!2 (not (= (select C (+ 2 B)) 0)))
      (a!3 (not (= (select C (+ 2 B)) A)))
      (a!4 (not (= (select C (+ 1 B)) 0)))
      (a!5 (not (= (select C (+ 1 B)) A))))
  (and (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) 0)
       a!1
       a!2
       a!3
       a!4
       a!5
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= (- 1) E)))
       (= (select F (+ 1 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) 0)))
      (a!2 (not (= (select F (+ 1 E)) D)))
      (a!3 (not (= (select C (+ 3 B)) A)))
      (a!4 (not (= (select C (+ 2 B)) 0)))
      (a!5 (not (= (select C (+ 2 B)) A)))
      (a!6 (not (= (select C (+ 1 B)) 0)))
      (a!7 (not (= (select C (+ 1 B)) A))))
  (and a!1
       a!2
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) 0)
       a!3
       a!4
       a!5
       a!6
       a!7
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (or (not (= C F)) (not (= (- 2) E)))
       (= (select F (+ 2 E)) D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 2 E)) D)))
      (a!2 (not (= (select F (+ 1 E)) 0)))
      (a!3 (not (= (select F (+ 1 E)) D)))
      (a!4 (not (= (select C (+ 3 B)) A)))
      (a!5 (not (= (select C (+ 2 B)) 0)))
      (a!6 (not (= (select C (+ 2 B)) A)))
      (a!7 (not (= (select C (+ 1 B)) 0)))
      (a!8 (not (= (select C (+ 1 B)) A))))
  (and (= (select F (+ 2 E)) 0)
       a!1
       a!2
       a!3
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) 0)
       a!4
       a!5
       a!6
       a!7
       a!8
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select F (+ 1 E)) D)))
      (a!2 (not (= (select C (+ 3 B)) A)))
      (a!3 (not (= (select C (+ 2 B)) 0)))
      (a!4 (not (= (select C (+ 2 B)) A)))
      (a!5 (not (= (select C (+ 1 B)) 0)))
      (a!6 (not (= (select C (+ 1 B)) A))))
  (and (= (select F (+ 1 E)) 0)
       a!1
       (not (= (select F E) 0))
       (not (= (select F E) D))
       (= (select C (+ 3 B)) 0)
       a!2
       a!3
       a!4
       a!5
       a!6
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B C D E F)
        (let ((a!1 (not (= (select C (+ 3 B)) A)))
      (a!2 (not (= (select C (+ 2 B)) 0)))
      (a!3 (not (= (select C (+ 2 B)) A)))
      (a!4 (not (= (select C (+ 1 B)) 0)))
      (a!5 (not (= (select C (+ 1 B)) A))))
  (and (= (select F E) 0)
       (not (= (select F E) D))
       (= (select C (+ 3 B)) 0)
       a!1
       a!2
       a!3
       a!4
       a!5
       (not (= (select C B) 0))
       (not (= (select C B) A))
       (not (= C F))))
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
