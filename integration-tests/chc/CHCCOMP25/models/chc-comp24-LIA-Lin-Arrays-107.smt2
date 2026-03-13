(set-logic HORN)


(declare-fun |INV_MAIN_1| ( Int Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)
(declare-fun |INV_MAIN_0| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F) (= v_6 A) (= 0 v_7))
      )
      (INV_MAIN_0 A B v_6 C v_7 E D F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I J K)
        (and (= (select G E) 0)
     (not (= (select G D) 0))
     (not (= (select K J) 0))
     (= (select K I) 0)
     (= C (+ 1 D))
     (= B (+ 1 H))
     (= A (+ 1 J))
     (not (= (select G E) (select G D))))
      )
      (INV_MAIN_0 C E F G B I A K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 B C D E F G H I)
        (let ((a!1 (or (not (= (select I G) 0)) (= (select I H) 0))))
  (and (= (select E C) 0)
       (not (= (select E B) 0))
       (= A (+ 1 B))
       a!1
       (not (= (select E C) (select E B)))))
      )
      (INV_MAIN_0 A C D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 C D E F G H I J)
        (let ((a!1 (or (= (select F D) (select F C))
               (not (= (select F D) 0))
               (= (select F C) 0))))
  (and (= (select J H) 0)
       (= B (+ 1 G))
       (= A (+ 1 I))
       a!1
       (not (= (select J I) 0))))
      )
      (INV_MAIN_0 C D E F B H A J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K (Array Int Int)) (v_11 Int) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I J K)
        (and (not (= (select G E) 0))
     (not (= (select G D) 0))
     (not (= (select K J) (select K I)))
     (not (= (select K J) 0))
     (not (= (select K I) 0))
     (= C (select G D))
     (= B (+ 1 D))
     (= A (+ 1 E))
     (not (= (select G E) (select G D)))
     (= 0 v_11))
      )
      (INV_MAIN_1 C B A E F G v_11 H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J K L M)
        (and (not (= (select H E) C))
     (= (select M (+ 1 K I)) 0)
     (= A (+ 1 L))
     (= B (+ 1 J))
     (= (select H E) 0))
      )
      (INV_MAIN_0 D F G H B K A M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J K L M)
        (let ((a!1 (not (= (select M (+ 1 K I)) 0)))
      (a!2 (not (= (select M L) (select M (+ 1 K I))))))
  (and (not (= (select H E) C))
       a!1
       a!2
       (= A (+ 1 I))
       (= B (+ 1 E))
       (not (= (select H E) 0))))
      )
      (INV_MAIN_1 C D B F G H A J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I J K L)
        (let ((a!1 (or (= (select L K) (select L (+ 1 J H))) (= (select L (+ 1 J H)) 0))))
  (and (not (= (select G D) B)) (= A (+ 1 D)) a!1 (not (= (select G D) 0))))
      )
      (INV_MAIN_1 B C A E F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I J K L)
        (let ((a!1 (not (= (select L K) (select L (+ 1 J H)))))
      (a!2 (not (= (select L (+ 1 J H)) 0))))
  (and a!1 (= A (+ 1 H)) (or (= (select G D) B) (= (select G D) 0)) a!2))
      )
      (INV_MAIN_1 B C D E F G A I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (and (not (= (select D A) 0))
     (not (= (select H G) (select H F)))
     (not (= (select H G) 0))
     (not (= (select H F) 0))
     (= (select D B) (select D A)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (and (not (= (select H G) (select H F)))
     (not (= (select H G) 0))
     (not (= (select H F) 0))
     (= (select D A) 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (and (not (= (select D B) 0))
     (not (= (select D A) 0))
     (= (select H G) (select H F))
     (not (= (select H G) 0))
     (not (= (select H F) 0))
     (not (= (select D B) (select D A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (and (not (= (select D B) 0))
     (not (= (select D A) 0))
     (= (select H G) 0)
     (not (= (select D B) (select D A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (let ((a!1 (not (= (+ A (* (- 1) C)) E))))
  (and (not (= (select D A) 0))
       (= (select H G) (select H F))
       (not (= (select H G) 0))
       (not (= (select H F) 0))
       (or a!1 (not (= D H)))
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
        (INV_MAIN_0 A B C D E F G H)
        (let ((a!1 (not (= (+ A (* (- 1) C)) 0))))
  (and (not (= (select D A) 0))
       (= (select H G) 0)
       (or (not (= D H)) a!1)
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
        (INV_MAIN_0 A B C D E F G H)
        (and (= (select H G) (select H F))
     (not (= (select H G) 0))
     (not (= (select H F) 0))
     (or (not (= D H)) (not (= 0 E)))
     (= (select D A) 0))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F G H)
        (and (= (select D A) 0) (= (select H G) 0) (not (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H I J K)
        (and (= (select K (+ 1 I G)) 0) (= (select F C) A))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H I J K)
        (let ((a!1 (not (= (select K (+ 1 I G)) 0))))
  (and (not (= (select F C) A))
       a!1
       (= (select K J) (select K (+ 1 I G)))
       (= (select F C) 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J Int) (K (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H I J K)
        (let ((a!1 (not (= (select K (+ 1 I G)) 0)))
      (a!2 (not (= (+ B (* (- 1) E)) (+ 1 H)))))
  (and a!1
       (= (select K J) (select K (+ 1 I G)))
       (or a!2 (not (= F K)))
       (= (select F C) A)))
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
