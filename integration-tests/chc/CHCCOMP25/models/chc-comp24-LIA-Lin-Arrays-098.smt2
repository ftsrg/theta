(set-logic HORN)


(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_2| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F) (= 0 v_6) (= 0 v_7))
      )
      (INV_MAIN_1 A v_6 B C D v_7 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (v_8 Int) (v_9 Int) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (and (not (<= C B)) (not (<= G F)) (= v_8 B) (= v_9 F))
      )
      (INV_MAIN_2 A B v_8 C D E F v_9 G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H I J K L)
        (and (= B (+ 1 D)) (<= F E) (<= K J) (= A (+ 1 I)))
      )
      (INV_MAIN_1 C B F G H A K L)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 E F G H I J K L M N)
        (let ((a!1 (store I (+ E (* 4 F)) (select I (+ E (* 4 G)))))
      (a!3 (<= (select I (+ E (* 4 G))) (select I (+ E (* 4 F)))))
      (a!4 (<= (select N (+ J (* 4 K))) (select N (+ J (* 4 L)))))
      (a!5 (store N (+ J (* 4 K)) (select N (+ J (* 4 L))))))
(let ((a!2 (store a!1 (+ E (* 4 G)) (select I (+ E (* 4 F)))))
      (a!6 (store a!5 (+ J (* 4 L)) (select N (+ J (* 4 K))))))
  (and (= C a!2)
       (= B (+ 1 L))
       (= D (+ 1 G))
       a!3
       (not a!4)
       (not (<= H G))
       (not (<= M L))
       (= A a!6))))
      )
      (INV_MAIN_2 E F D H C J K B M A)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 D E F G H I J K L M)
        (let ((a!1 (<= (select H (+ D (* 4 F))) (select H (+ D (* 4 E)))))
      (a!2 (<= (select M (+ I (* 4 J))) (select M (+ I (* 4 K)))))
      (a!3 (store H (+ D (* 4 E)) (select H (+ D (* 4 F))))))
(let ((a!4 (store a!3 (+ D (* 4 F)) (select H (+ D (* 4 E))))))
  (and (= A (+ 1 K))
       (= C (+ 1 F))
       a!1
       a!2
       (not (<= G F))
       (not (<= L K))
       (= B a!4))))
      )
      (INV_MAIN_2 D E C G B I J A L M)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 D E F G H I J K L M)
        (let ((a!1 (<= (select H (+ D (* 4 F))) (select H (+ D (* 4 E)))))
      (a!2 (<= (select M (+ I (* 4 J))) (select M (+ I (* 4 K)))))
      (a!3 (store M (+ I (* 4 J)) (select M (+ I (* 4 K))))))
(let ((a!4 (store a!3 (+ I (* 4 K)) (select M (+ I (* 4 J))))))
  (and (= B (+ 1 K))
       (= C (+ 1 F))
       (not a!1)
       (not a!2)
       (not (<= G F))
       (not (<= L K))
       (= A a!4))))
      )
      (INV_MAIN_2 D E C G H I J B L A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H I J K L)
        (let ((a!1 (<= (select G (+ C (* 4 E))) (select G (+ C (* 4 D)))))
      (a!2 (<= (select L (+ H (* 4 I))) (select L (+ H (* 4 J))))))
  (and (= B (+ 1 E)) (not a!1) a!2 (not (<= F E)) (not (<= K J)) (= A (+ 1 J))))
      )
      (INV_MAIN_2 C D B F G H I A K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (and (<= C B) (not (<= G F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (and (not (<= C B)) (<= G F))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A B C D E F G H)
        (and (<= G F) (<= C B) (not (= D H)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H I J)
        (let ((a!1 (<= (select J (+ F (* 4 G))) (select J (+ F (* 4 H))))))
  (and (<= D C) (not (<= I H)) (not a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H I J)
        (let ((a!1 (<= (select J (+ F (* 4 G))) (select J (+ F (* 4 H))))))
  (and (<= D C) (not (<= I H)) a!1))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H I J)
        (let ((a!1 (<= (select E (+ A (* 4 C))) (select E (+ A (* 4 B))))))
  (and (not (<= D C)) (<= I H) a!1))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H I J)
        (let ((a!1 (<= (select E (+ A (* 4 C))) (select E (+ A (* 4 B))))))
  (and (not (<= D C)) (<= I H) (not a!1)))
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
