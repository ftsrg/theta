(set-logic HORN)


(declare-fun |INV_MAIN_3| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |INV_MAIN_2| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) ) 
    (=>
      (and
        (and (= C (store I H E))
     (= I N)
     (= B (+ (- 1) K))
     (= D (+ (- 1) F))
     (not (= K 0))
     (= H M)
     (= G L)
     (not (= F 0))
     (= F K)
     (= E J)
     (>= M 0)
     (>= L 0)
     (>= J 0)
     (>= H 0)
     (>= G 0)
     (>= E 0)
     (= A (store N M J)))
      )
      (INV_MAIN_1 G D E C L B J A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H I J)
        (let ((a!1 (not (= (select J (+ I H)) 41)))
      (a!2 (not (= (select F (+ E D)) 41))))
  (and a!1 (not (= H 0)) (not (= D 0)) (= B (+ (- 1) D)) (= A (+ (- 1) H)) a!2))
      )
      (INV_MAIN_1 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I)
        (let ((a!1 (or (= G 0) (= (select I (+ H G)) 41)))
      (a!2 (not (= (select E (+ D C)) 41))))
  (and (not (= C 0)) (= A (+ (- 1) C)) a!1 a!2))
      )
      (INV_MAIN_1 B A D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 B C D E F G H I)
        (let ((a!1 (or (= C 0) (= (select E (+ D C)) 41)))
      (a!2 (not (= (select I (+ H G)) 41))))
  (and (not (= G 0)) (= A (+ (- 1) G)) a!1 a!2))
      )
      (INV_MAIN_1 B C D E F A H I)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L)
        (and (= C (store H (+ G F) 0))
     (= (select H (+ G F)) 41)
     (= (select L (+ K J)) 41)
     (= B (+ 1 J))
     (not (= J 0))
     (not (= F 0))
     (= D (+ 1 F))
     (= A (store L (+ K J) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L)
        (and (= C (store H (+ G F) 0))
     (= (select H (+ G F)) 41)
     (= (select L (+ K J)) 41)
     (= B (+ 1 J))
     (= J 0)
     (not (= F 0))
     (= D (+ 1 F))
     (= A (store L (+ K J) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L)
        (and (= C (store H (+ G F) 0))
     (= (select H (+ G F)) 41)
     (= (select L (+ K J)) 41)
     (= B (+ 1 J))
     (not (= J 0))
     (= F 0)
     (= D (+ 1 F))
     (= A (store L (+ K J) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J K L)
        (and (= C (store H (+ G F) 0))
     (= (select H (+ G F)) 41)
     (= (select L (+ K J)) 41)
     (= B (+ 1 J))
     (= J 0)
     (= F 0)
     (= D (+ 1 F))
     (= A (store L (+ K J) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H I J)
        (and (= (select J (+ I H)) 32)
     (= B (+ 1 D))
     (= A (+ 1 H))
     (= (select F (+ E D)) 32))
      )
      (INV_MAIN_2 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H I J)
        (let ((a!1 (not (= (select J (+ I H)) 32))))
  (and (= (select J (+ I H)) 9)
       a!1
       (= B (+ 1 D))
       (= A (+ 1 H))
       (= (select F (+ E D)) 32)))
      )
      (INV_MAIN_2 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H I J)
        (let ((a!1 (not (= (select F (+ E D)) 32))))
  (and a!1
       (= (select J (+ I H)) 32)
       (= B (+ 1 D))
       (= A (+ 1 H))
       (= (select F (+ E D)) 9)))
      )
      (INV_MAIN_2 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 C D E F G H I J)
        (let ((a!1 (not (= (select F (+ E D)) 32)))
      (a!2 (not (= (select J (+ I H)) 32))))
  (and a!1
       (= (select J (+ I H)) 9)
       a!2
       (= B (+ 1 D))
       (= A (+ 1 H))
       (= (select F (+ E D)) 9)))
      )
      (INV_MAIN_2 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 B C D E F G H I)
        (let ((a!1 (not (= (select I (+ H G)) 32)))
      (a!2 (not (= (select I (+ H G)) 9))))
(let ((a!3 (or (= (select I (+ H G)) 32) a!2)))
  (and a!1 (= A (+ 1 C)) a!3 (= (select E (+ D C)) 32))))
      )
      (INV_MAIN_2 B A D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 B C D E F G H I)
        (let ((a!1 (not (= (select E (+ D C)) 32)))
      (a!2 (not (= (select I (+ H G)) 32)))
      (a!3 (not (= (select I (+ H G)) 9))))
(let ((a!4 (or (= (select I (+ H G)) 32) a!3)))
  (and a!1 a!2 (= A (+ 1 C)) a!4 (= (select E (+ D C)) 9))))
      )
      (INV_MAIN_2 B A D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 B C D E F G H I)
        (let ((a!1 (not (= (select E (+ D C)) 9)))
      (a!3 (not (= (select E (+ D C)) 32))))
(let ((a!2 (or (= (select E (+ D C)) 32) a!1)))
  (and (= (select I (+ H G)) 32) (= A (+ 1 G)) a!2 a!3)))
      )
      (INV_MAIN_2 B C D E F A H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 B C D E F G H I)
        (let ((a!1 (not (= (select I (+ H G)) 32)))
      (a!2 (not (= (select E (+ D C)) 9)))
      (a!4 (not (= (select E (+ D C)) 32))))
(let ((a!3 (or (= (select E (+ D C)) 32) a!2)))
  (and (= (select I (+ H G)) 9) a!1 (= A (+ 1 G)) a!3 a!4)))
      )
      (INV_MAIN_2 B C D E F A H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H)
        (let ((a!1 (not (= (select D (+ C B)) 32)))
      (a!2 (not (= (select H (+ G F)) 9)))
      (a!3 (not (= (select H (+ G F)) 32)))
      (a!4 (not (= (select D (+ C B)) 9))))
  (and (= (select D (+ C B)) 61) a!1 a!2 (= (select H (+ G F)) 61) a!3 a!4))
      )
      (INV_MAIN_3 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 C D E F G H I J)
        (and (= (select J (+ 1 I H)) 32)
     (= B (+ 1 D))
     (= A (+ 1 H))
     (= (select F (+ 1 E D)) 32))
      )
      (INV_MAIN_3 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 C D E F G H I J)
        (let ((a!1 (not (= (select J (+ 1 I H)) 32))))
  (and (= (select J (+ 1 I H)) 9)
       a!1
       (= B (+ 1 D))
       (= A (+ 1 H))
       (= (select F (+ 1 E D)) 32)))
      )
      (INV_MAIN_3 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 C D E F G H I J)
        (let ((a!1 (not (= (select F (+ 1 E D)) 32))))
  (and a!1
       (= (select J (+ 1 I H)) 32)
       (= B (+ 1 D))
       (= A (+ 1 H))
       (= (select F (+ 1 E D)) 9)))
      )
      (INV_MAIN_3 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 C D E F G H I J)
        (let ((a!1 (not (= (select F (+ 1 E D)) 32)))
      (a!2 (not (= (select J (+ 1 I H)) 32))))
  (and a!1
       (= (select J (+ 1 I H)) 9)
       a!2
       (= B (+ 1 D))
       (= A (+ 1 H))
       (= (select F (+ 1 E D)) 9)))
      )
      (INV_MAIN_3 C B E F G A I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 B C D E F G H I)
        (let ((a!1 (not (= (select I (+ 1 H G)) 32)))
      (a!2 (not (= (select I (+ 1 H G)) 9))))
(let ((a!3 (or (= (select I (+ 1 H G)) 32) a!2)))
  (and a!1 (= A (+ 1 C)) a!3 (= (select E (+ 1 D C)) 32))))
      )
      (INV_MAIN_3 B A D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 B C D E F G H I)
        (let ((a!1 (not (= (select E (+ 1 D C)) 32)))
      (a!2 (not (= (select I (+ 1 H G)) 32)))
      (a!3 (not (= (select I (+ 1 H G)) 9))))
(let ((a!4 (or (= (select I (+ 1 H G)) 32) a!3)))
  (and a!1 a!2 (= A (+ 1 C)) a!4 (= (select E (+ 1 D C)) 9))))
      )
      (INV_MAIN_3 B A D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 B C D E F G H I)
        (let ((a!1 (not (= (select E (+ 1 D C)) 9)))
      (a!3 (not (= (select E (+ 1 D C)) 32))))
(let ((a!2 (or (= (select E (+ 1 D C)) 32) a!1)))
  (and (= (select I (+ 1 H G)) 32) (= A (+ 1 G)) a!2 a!3)))
      )
      (INV_MAIN_3 B C D E F A H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 B C D E F G H I)
        (let ((a!1 (not (= (select I (+ 1 H G)) 32)))
      (a!2 (not (= (select E (+ 1 D C)) 9)))
      (a!4 (not (= (select E (+ 1 D C)) 32))))
(let ((a!3 (or (= (select E (+ 1 D C)) 32) a!2)))
  (and (= (select I (+ 1 H G)) 9) a!1 (= A (+ 1 G)) a!3 a!4)))
      )
      (INV_MAIN_3 B C D E F A H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) ) 
    (=>
      (and
        (and (= G 0)
     (= D I)
     (= C H)
     (not (= B 0))
     (= B G)
     (= A F)
     (>= I 0)
     (>= H 0)
     (>= F 0)
     (>= D 0)
     (>= C 0)
     (>= A 0)
     (= E J))
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
        (let ((a!1 (not (= (select D (+ C B)) 41))))
  (and (= (select H (+ G F)) 41) (not (= F 0)) (= B 0) a!1))
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
        (let ((a!1 (not (= (select D (+ C B)) 41))))
  (and (= (select H (+ G F)) 41) (= F 0) (= B 0) a!1))
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
        (let ((a!1 (not (= (select H (+ G F)) 41))))
  (and a!1 (= F 0) (not (= B 0)) (= (select D (+ C B)) 41)))
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
        (let ((a!1 (not (= (select H (+ G F)) 41))))
  (and a!1 (= F 0) (= B 0) (= (select D (+ C B)) 41)))
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
        (let ((a!1 (not (= (select D (+ C B)) 41)))
      (a!2 (not (= (select H (+ G F)) 41))))
  (and a!1 a!2 (= F 0) (= B 0) (not (= D H))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H)
        (let ((a!1 (not (= (select D (+ C B)) 61)))
      (a!2 (not (= (select D (+ C B)) 32)))
      (a!3 (not (= (select H (+ G F)) 9)))
      (a!4 (not (= (select H (+ G F)) 32)))
      (a!5 (not (= (select D (+ C B)) 9))))
  (and a!1 a!2 a!3 (= (select H (+ G F)) 61) a!4 a!5))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H)
        (let ((a!1 (not (= (select D (+ C B)) 32)))
      (a!2 (not (= (select H (+ G F)) 9)))
      (a!3 (not (= (select H (+ G F)) 61)))
      (a!4 (not (= (select H (+ G F)) 32)))
      (a!5 (not (= (select D (+ C B)) 9))))
  (and (= (select D (+ C B)) 61) a!1 a!2 a!3 a!4 a!5))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A B C D E F G H)
        (let ((a!1 (not (= (select D (+ C B)) 9)))
      (a!2 (not (= (select D (+ C B)) 61)))
      (a!3 (not (= (select D (+ C B)) 32)))
      (a!4 (not (= (select H (+ G F)) 9)))
      (a!5 (not (= (select H (+ G F)) 61)))
      (a!6 (not (= (select H (+ G F)) 32))))
  (and a!1 a!2 a!3 a!4 a!5 a!6 (not (= D H))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_3 A B C D E F G H)
        (let ((a!1 (not (= (select D (+ 1 C B)) 9)))
      (a!2 (not (= (select D (+ 1 C B)) 32)))
      (a!3 (not (= (select H (+ 1 G F)) 9)))
      (a!4 (not (= (select H (+ 1 G F)) 32)))
      (a!5 (not (= (store D A (+ 1 C B)) (store H E (+ 1 G F))))))
  (and a!1 a!2 a!3 a!4 a!5))
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
