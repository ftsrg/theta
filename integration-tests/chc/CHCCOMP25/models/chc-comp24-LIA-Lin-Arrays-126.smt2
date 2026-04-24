(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (and (= (select F D) B) (or (not (= E F)) (not (= C D))) (= (select E C) A))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (or (not (= E F)) (not (= C (+ 1 D))))))
  (and (= (select F (+ 1 D)) B)
       (not (= (select F D) 0))
       (not (= (select F D) B))
       a!1
       (= (select E C) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select F (+ 1 D)) 0)))
      (a!2 (not (= (select F (+ 1 D)) B)))
      (a!3 (or (not (= E F)) (not (= C (+ 2 D))))))
  (and a!1
       a!2
       (= (select F (+ 2 D)) B)
       (not (= (select F D) 0))
       (not (= (select F D) B))
       a!3
       (= (select E C) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select F (+ 1 C)) 0)))
      (a!2 (not (= (select F (+ 1 C)) B)))
      (a!3 (not (= (select F (+ 2 C)) B))))
  (and a!1
       a!2
       (= (select F (+ 2 C)) 0)
       a!3
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D 0)))
       (= (select E D) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select F (+ 1 C)) B))))
  (and (= (select F (+ 1 C)) 0)
       a!1
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D 0)))
       (= (select E D) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (and (= (select F C) 0)
     (not (= (select F C) B))
     (or (not (= E F)) (not (= D 0)))
     (= (select E D) A))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (and (not (= (select E B) A))
     (= (select F D) C)
     (or (not (= E F)) (not (= 0 D)))
     (= (select E B) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (and (not (= (select E B) A))
     (= (select F (+ 1 D)) C)
     (not (= (select F D) 0))
     (not (= (select F D) C))
     (or (not (= E F)) (not (= (- 1) D)))
     (= (select E B) 0))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select F (+ 1 D)) 0))) (a!2 (not (= (select F (+ 1 D)) C))))
  (and (not (= (select E B) A))
       a!1
       a!2
       (= (select F (+ 2 D)) C)
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (or (not (= E F)) (not (= (- 2) D)))
       (= (select E B) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select F (+ 1 D)) 0)))
      (a!2 (not (= (select F (+ 1 D)) C)))
      (a!3 (not (= (select F (+ 2 D)) C))))
  (and (= (select E B) 0)
       (not (= (select E B) A))
       a!1
       a!2
       (= (select F (+ 2 D)) 0)
       a!3
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select F (+ 1 D)) C))))
  (and (= (select E B) 0)
       (not (= (select E B) A))
       (= (select F (+ 1 D)) 0)
       a!1
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (and (= (select E B) 0)
     (not (= (select E B) A))
     (= (select F D) 0)
     (not (= (select F D) C))
     (not (= E F)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (or (not (= E F)) (not (= C (+ (- 1) D))))))
  (and (not (= (select E C) 0))
       (not (= (select E C) A))
       (= (select F D) B)
       a!1
       (= (select E (+ 1 C)) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (and (not (= (select E C) 0))
     (not (= (select E C) A))
     (= (select F (+ 1 D)) B)
     (not (= (select F D) 0))
     (not (= (select F D) B))
     (or (not (= E F)) (not (= C D)))
     (= (select E (+ 1 C)) A))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select F (+ 1 D)) 0)))
      (a!2 (not (= (select F (+ 1 D)) B)))
      (a!3 (or (not (= E F)) (not (= C (+ 1 D))))))
  (and (not (= (select E C) 0))
       (not (= (select E C) A))
       a!1
       a!2
       (= (select F (+ 2 D)) B)
       (not (= (select F D) 0))
       (not (= (select F D) B))
       a!3
       (= (select E (+ 1 C)) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select F (+ 1 C)) 0)))
      (a!2 (not (= (select F (+ 1 C)) B)))
      (a!3 (not (= (select F (+ 2 C)) B))))
  (and (not (= (select E D) 0))
       (not (= (select E D) A))
       a!1
       a!2
       (= (select F (+ 2 C)) 0)
       a!3
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 1))))
       (= (select E (+ 1 D)) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select F (+ 1 C)) B))))
  (and (not (= (select E D) 0))
       (not (= (select E D) A))
       (= (select F (+ 1 C)) 0)
       a!1
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 1))))
       (= (select E (+ 1 D)) A)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (and (not (= (select E D) 0))
     (not (= (select E D) A))
     (= (select F C) 0)
     (not (= (select F C) B))
     (or (not (= E F)) (not (= D (- 1))))
     (= (select E (+ 1 D)) A))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A))))
  (and a!1
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F D) C)
       (or (not (= E F)) (not (= 0 D)))
       (= (select E (+ 1 B)) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A))))
  (and a!1
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F (+ 1 D)) C)
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (or (not (= E F)) (not (= (- 1) D)))
       (= (select E (+ 1 B)) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select F (+ 1 D)) 0)))
      (a!3 (not (= (select F (+ 1 D)) C))))
  (and a!1
       (not (= (select E B) 0))
       (not (= (select E B) A))
       a!2
       a!3
       (= (select F (+ 2 D)) C)
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (or (not (= E F)) (not (= (- 2) D)))
       (= (select E (+ 1 B)) 0)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select F (+ 1 D)) 0)))
      (a!3 (not (= (select F (+ 1 D)) C)))
      (a!4 (not (= (select F (+ 2 D)) C))))
  (and (= (select E (+ 1 B)) 0)
       a!1
       (not (= (select E B) 0))
       (not (= (select E B) A))
       a!2
       a!3
       (= (select F (+ 2 D)) 0)
       a!4
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A))) (a!2 (not (= (select F (+ 1 D)) C))))
  (and (= (select E (+ 1 B)) 0)
       a!1
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F (+ 1 D)) 0)
       a!2
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A))))
  (and (= (select E (+ 1 B)) 0)
       a!1
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F D) 0)
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select E (+ 1 C)) A)))
      (a!2 (or (not (= E F)) (not (= C (+ (- 2) D)))))
      (a!3 (not (= (select E (+ 1 C)) 0))))
  (and a!1
       (= (select E (+ 2 C)) A)
       (not (= (select E C) 0))
       (not (= (select E C) A))
       (= (select F D) B)
       a!2
       a!3))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select E (+ 1 C)) A)))
      (a!2 (or (not (= E F)) (not (= C (+ (- 1) D)))))
      (a!3 (not (= (select E (+ 1 C)) 0))))
  (and a!1
       (= (select E (+ 2 C)) A)
       (not (= (select E C) 0))
       (not (= (select E C) A))
       (= (select F (+ 1 D)) B)
       (not (= (select F D) 0))
       (not (= (select F D) B))
       a!2
       a!3))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select E (+ 1 C)) A)))
      (a!2 (not (= (select F (+ 1 D)) 0)))
      (a!3 (not (= (select F (+ 1 D)) B)))
      (a!4 (not (= (select E (+ 1 C)) 0))))
  (and a!1
       (= (select E (+ 2 C)) A)
       (not (= (select E C) 0))
       (not (= (select E C) A))
       a!2
       a!3
       (= (select F (+ 2 D)) B)
       (not (= (select F D) 0))
       (not (= (select F D) B))
       (or (not (= E F)) (not (= C D)))
       a!4))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select E (+ 1 D)) A)))
      (a!2 (not (= (select F (+ 1 C)) 0)))
      (a!3 (not (= (select F (+ 1 C)) B)))
      (a!4 (not (= (select F (+ 2 C)) B)))
      (a!5 (not (= (select E (+ 1 D)) 0))))
  (and a!1
       (= (select E (+ 2 D)) A)
       (not (= (select E D) 0))
       (not (= (select E D) A))
       a!2
       a!3
       (= (select F (+ 2 C)) 0)
       a!4
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 2))))
       a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select E (+ 1 D)) A)))
      (a!2 (not (= (select F (+ 1 C)) B)))
      (a!3 (not (= (select E (+ 1 D)) 0))))
  (and a!1
       (= (select E (+ 2 D)) A)
       (not (= (select E D) 0))
       (not (= (select E D) A))
       (= (select F (+ 1 C)) 0)
       a!2
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 2))))
       a!3))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select E (+ 1 D)) A))) (a!2 (not (= (select E (+ 1 D)) 0))))
  (and a!1
       (= (select E (+ 2 D)) A)
       (not (= (select E D) 0))
       (not (= (select E D) A))
       (= (select F C) 0)
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 2))))
       a!2))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select E (+ 2 B)) A)))
      (a!3 (not (= (select E (+ 1 B)) 0))))
  (and a!1
       (= (select E (+ 2 B)) 0)
       a!2
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F D) C)
       (or (not (= E F)) (not (= 0 D)))
       a!3))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select E (+ 2 B)) A)))
      (a!3 (not (= (select E (+ 1 B)) 0))))
  (and a!1
       (= (select E (+ 2 B)) 0)
       a!2
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F (+ 1 D)) C)
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (or (not (= E F)) (not (= (- 1) D)))
       a!3))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select E (+ 2 B)) A)))
      (a!3 (not (= (select F (+ 1 D)) 0)))
      (a!4 (not (= (select F (+ 1 D)) C)))
      (a!5 (not (= (select E (+ 1 B)) 0))))
  (and a!1
       (= (select E (+ 2 B)) 0)
       a!2
       (not (= (select E B) 0))
       (not (= (select E B) A))
       a!3
       a!4
       (= (select F (+ 2 D)) C)
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (or (not (= E F)) (not (= (- 2) D)))
       a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) 0)))
      (a!2 (not (= (select E (+ 1 B)) A)))
      (a!3 (not (= (select E (+ 2 B)) A)))
      (a!4 (not (= (select F (+ 1 D)) 0)))
      (a!5 (not (= (select F (+ 1 D)) C)))
      (a!6 (not (= (select F (+ 2 D)) C))))
  (and a!1
       a!2
       (= (select E (+ 2 B)) 0)
       a!3
       (not (= (select E B) 0))
       (not (= (select E B) A))
       a!4
       a!5
       (= (select F (+ 2 D)) 0)
       a!6
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) 0)))
      (a!2 (not (= (select E (+ 1 B)) A)))
      (a!3 (not (= (select E (+ 2 B)) A)))
      (a!4 (not (= (select F (+ 1 D)) C))))
  (and a!1
       a!2
       (= (select E (+ 2 B)) 0)
       a!3
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F (+ 1 D)) 0)
       a!4
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) 0)))
      (a!2 (not (= (select E (+ 1 B)) A)))
      (a!3 (not (= (select E (+ 2 B)) A))))
  (and a!1
       a!2
       (= (select E (+ 2 B)) 0)
       a!3
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F D) 0)
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select E (+ 1 C)) A)))
      (a!2 (not (= (select E (+ 2 C)) 0)))
      (a!3 (not (= (select E (+ 2 C)) A)))
      (a!4 (or (not (= E F)) (not (= C (+ (- 3) D)))))
      (a!5 (not (= (select E (+ 1 C)) 0))))
  (and a!1
       (= (select E (+ 3 C)) A)
       a!2
       a!3
       (not (= (select E C) 0))
       (not (= (select E C) A))
       (= (select F D) B)
       a!4
       a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select E (+ 1 C)) A)))
      (a!2 (not (= (select E (+ 2 C)) 0)))
      (a!3 (not (= (select E (+ 2 C)) A)))
      (a!4 (or (not (= E F)) (not (= C (+ (- 2) D)))))
      (a!5 (not (= (select E (+ 1 C)) 0))))
  (and a!1
       (= (select E (+ 3 C)) A)
       a!2
       a!3
       (not (= (select E C) 0))
       (not (= (select E C) A))
       (= (select F (+ 1 D)) B)
       (not (= (select F D) 0))
       (not (= (select F D) B))
       a!4
       a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A C E B D F)
        (let ((a!1 (not (= (select E (+ 1 C)) A)))
      (a!2 (not (= (select E (+ 2 C)) 0)))
      (a!3 (not (= (select E (+ 2 C)) A)))
      (a!4 (not (= (select F (+ 1 D)) 0)))
      (a!5 (not (= (select F (+ 1 D)) B)))
      (a!6 (or (not (= E F)) (not (= C (+ (- 1) D)))))
      (a!7 (not (= (select E (+ 1 C)) 0))))
  (and a!1
       (= (select E (+ 3 C)) A)
       a!2
       a!3
       (not (= (select E C) 0))
       (not (= (select E C) A))
       a!4
       a!5
       (= (select F (+ 2 D)) B)
       (not (= (select F D) 0))
       (not (= (select F D) B))
       a!6
       a!7))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select E (+ 1 D)) A)))
      (a!2 (not (= (select E (+ 2 D)) 0)))
      (a!3 (not (= (select E (+ 2 D)) A)))
      (a!4 (not (= (select F (+ 1 C)) 0)))
      (a!5 (not (= (select F (+ 1 C)) B)))
      (a!6 (not (= (select F (+ 2 C)) B)))
      (a!7 (not (= (select E (+ 1 D)) 0))))
  (and a!1
       (= (select E (+ 3 D)) A)
       a!2
       a!3
       (not (= (select E D) 0))
       (not (= (select E D) A))
       a!4
       a!5
       (= (select F (+ 2 C)) 0)
       a!6
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 3))))
       a!7))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select E (+ 1 D)) A)))
      (a!2 (not (= (select E (+ 2 D)) 0)))
      (a!3 (not (= (select E (+ 2 D)) A)))
      (a!4 (not (= (select F (+ 1 C)) B)))
      (a!5 (not (= (select E (+ 1 D)) 0))))
  (and a!1
       (= (select E (+ 3 D)) A)
       a!2
       a!3
       (not (= (select E D) 0))
       (not (= (select E D) A))
       (= (select F (+ 1 C)) 0)
       a!4
       (not (= (select F C) 0))
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 3))))
       a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A D E B C F)
        (let ((a!1 (not (= (select E (+ 1 D)) A)))
      (a!2 (not (= (select E (+ 2 D)) 0)))
      (a!3 (not (= (select E (+ 2 D)) A)))
      (a!4 (not (= (select E (+ 1 D)) 0))))
  (and a!1
       (= (select E (+ 3 D)) A)
       a!2
       a!3
       (not (= (select E D) 0))
       (not (= (select E D) A))
       (= (select F C) 0)
       (not (= (select F C) B))
       (or (not (= E F)) (not (= D (- 3))))
       a!4))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select E (+ 3 B)) A)))
      (a!3 (not (= (select E (+ 2 B)) 0)))
      (a!4 (not (= (select E (+ 2 B)) A)))
      (a!5 (not (= (select E (+ 1 B)) 0))))
  (and a!1
       (= (select E (+ 3 B)) 0)
       a!2
       a!3
       a!4
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F D) C)
       (or (not (= E F)) (not (= 0 D)))
       a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select E (+ 3 B)) A)))
      (a!3 (not (= (select E (+ 2 B)) 0)))
      (a!4 (not (= (select E (+ 2 B)) A)))
      (a!5 (not (= (select E (+ 1 B)) 0))))
  (and a!1
       (= (select E (+ 3 B)) 0)
       a!2
       a!3
       a!4
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F (+ 1 D)) C)
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (or (not (= E F)) (not (= (- 1) D)))
       a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) A)))
      (a!2 (not (= (select E (+ 3 B)) A)))
      (a!3 (not (= (select E (+ 2 B)) 0)))
      (a!4 (not (= (select E (+ 2 B)) A)))
      (a!5 (not (= (select F (+ 1 D)) 0)))
      (a!6 (not (= (select F (+ 1 D)) C)))
      (a!7 (not (= (select E (+ 1 B)) 0))))
  (and a!1
       (= (select E (+ 3 B)) 0)
       a!2
       a!3
       a!4
       (not (= (select E B) 0))
       (not (= (select E B) A))
       a!5
       a!6
       (= (select F (+ 2 D)) C)
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (or (not (= E F)) (not (= (- 2) D)))
       a!7))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) 0)))
      (a!2 (not (= (select E (+ 1 B)) A)))
      (a!3 (not (= (select E (+ 3 B)) A)))
      (a!4 (not (= (select E (+ 2 B)) 0)))
      (a!5 (not (= (select E (+ 2 B)) A)))
      (a!6 (not (= (select F (+ 1 D)) 0)))
      (a!7 (not (= (select F (+ 1 D)) C)))
      (a!8 (not (= (select F (+ 2 D)) C))))
  (and a!1
       a!2
       (= (select E (+ 3 B)) 0)
       a!3
       a!4
       a!5
       (not (= (select E B) 0))
       (not (= (select E B) A))
       a!6
       a!7
       (= (select F (+ 2 D)) 0)
       a!8
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) 0)))
      (a!2 (not (= (select E (+ 1 B)) A)))
      (a!3 (not (= (select E (+ 3 B)) A)))
      (a!4 (not (= (select E (+ 2 B)) 0)))
      (a!5 (not (= (select E (+ 2 B)) A)))
      (a!6 (not (= (select F (+ 1 D)) C))))
  (and a!1
       a!2
       (= (select E (+ 3 B)) 0)
       a!3
       a!4
       a!5
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F (+ 1 D)) 0)
       a!6
       (not (= (select F D) 0))
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B E C D F)
        (let ((a!1 (not (= (select E (+ 1 B)) 0)))
      (a!2 (not (= (select E (+ 1 B)) A)))
      (a!3 (not (= (select E (+ 3 B)) A)))
      (a!4 (not (= (select E (+ 2 B)) 0)))
      (a!5 (not (= (select E (+ 2 B)) A))))
  (and a!1
       a!2
       (= (select E (+ 3 B)) 0)
       a!3
       a!4
       a!5
       (not (= (select E B) 0))
       (not (= (select E B) A))
       (= (select F D) 0)
       (not (= (select F D) C))
       (not (= E F))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 C D E F G H)
        (let ((a!1 (not (= (select H (+ 1 G)) F)))
      (a!2 (not (= (select H (+ 2 G)) 0)))
      (a!3 (not (= (select H (+ 2 G)) F)))
      (a!4 (not (= (select E (+ 1 D)) 0)))
      (a!5 (not (= (select E (+ 1 D)) C)))
      (a!6 (not (= (select E (+ 3 D)) 0)))
      (a!7 (not (= (select E (+ 3 D)) C)))
      (a!8 (not (= (select E (+ 2 D)) 0)))
      (a!9 (not (= (select E (+ 2 D)) C)))
      (a!10 (not (= (select H (+ 1 G)) 0))))
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
       (= B (+ 3 D))
       (= A (+ 3 G))
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
        (let ((a!1 (not (= (select D (+ 1 C)) B)))
      (a!2 (not (= (select D (+ 3 C)) 0)))
      (a!3 (not (= (select D (+ 3 C)) B)))
      (a!4 (not (= (select D (+ 2 C)) 0)))
      (a!5 (not (= (select D (+ 2 C)) B)))
      (a!6 (or (= (select G F) E)
               (= (select G (+ 1 F)) 0)
               (= (select G (+ 1 F)) E)
               (= (select G F) 0)
               (= (select G (+ 2 F)) E)
               (= (select G (+ 2 F)) 0)))
      (a!7 (not (= (select D (+ 1 C)) 0))))
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
        (let ((a!1 (not (= (select G (+ 1 F)) E)))
      (a!2 (not (= (select G (+ 2 F)) 0)))
      (a!3 (not (= (select G (+ 2 F)) E)))
      (a!4 (or (= (select D C) 0)
               (= (select D C) B)
               (= (select D (+ 3 C)) 0)
               (= (select D (+ 3 C)) B)
               (= (select D (+ 2 C)) 0)
               (= (select D (+ 2 C)) B)
               (= (select D (+ 1 C)) 0)
               (= (select D (+ 1 C)) B)))
      (a!5 (not (= (select G (+ 1 F)) 0))))
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
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        END_QUERY
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
