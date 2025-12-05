(set-logic HORN)


(declare-fun |INV_MAIN_3| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)
(declare-fun |INV_MAIN_2| ( Int Int Int (Array Int Int) Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (and (= E H)
     (= J 0)
     (not (= I 0))
     (= I J)
     (= D G)
     (= C F)
     (>= E 0)
     (>= H 0)
     (>= G 0)
     (>= F 0)
     (>= D 0)
     (>= C 0)
     (= A B))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F Int) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) (N Int) ) 
    (=>
      (and
        (and (= A (store L M N))
     (= C (store G H I))
     (= D (+ (- 1) F))
     (= I N)
     (not (= K 0))
     (= H M)
     (not (= F 0))
     (= F K)
     (= E J)
     (= B (+ (- 1) K))
     (>= I 0)
     (>= N 0)
     (>= M 0)
     (>= J 0)
     (>= H 0)
     (>= E 0)
     (= G L))
      )
      (INV_MAIN_1 E D I C J B N A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E D C B H G F)
        (let ((a!1 (not (= (select C (+ D E)) 41))))
  (and a!1 (not (= H 0)) (= E 0) (= (select F (+ G H)) 41)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E D C B H G F)
        (let ((a!1 (not (= (select C (+ D E)) 41))))
  (and a!1 (= H 0) (= E 0) (= (select F (+ G H)) 41)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E D C B H G F)
        (let ((a!1 (not (= (select F (+ G H)) 41))))
  (and (= (select C (+ D E)) 41) (= H 0) (not (= E 0)) a!1))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 A E D C B H G F)
        (let ((a!1 (not (= (select F (+ G H)) 41))))
  (and (= (select C (+ D E)) 41) (= H 0) (= E 0) a!1))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_1 A D C G B F E H)
        (let ((a!1 (not (= (select G (+ C D)) 41)))
      (a!2 (not (= (select H (+ E F)) 41))))
  (and a!1 a!2 (= F 0) (= D 0) (not (= G H))))
      )
      END_QUERY
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
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_1 E H G F I L K J)
        (and (= C (store F (+ G H) 0))
     (= (select F (+ G H)) 41)
     (= (select J (+ K L)) 41)
     (= B (+ 1 L))
     (not (= L 0))
     (not (= H 0))
     (= D (+ 1 H))
     (= A (store J (+ K L) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_1 E H G F I L K J)
        (and (= C (store F (+ G H) 0))
     (= (select F (+ G H)) 41)
     (= (select J (+ K L)) 41)
     (= B (+ 1 L))
     (= L 0)
     (not (= H 0))
     (= D (+ 1 H))
     (= A (store J (+ K L) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_1 E H G F I L K J)
        (and (= C (store F (+ G H) 0))
     (= (select F (+ G H)) 41)
     (= (select J (+ K L)) 41)
     (= B (+ 1 L))
     (not (= L 0))
     (= H 0)
     (= D (+ 1 H))
     (= A (store J (+ K L) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) ) 
    (=>
      (and
        (INV_MAIN_1 E H G F I L K J)
        (and (= C (store F (+ G H) 0))
     (= (select F (+ G H)) 41)
     (= (select J (+ K L)) 41)
     (= B (+ 1 L))
     (= L 0)
     (= H 0)
     (= D (+ 1 H))
     (= A (store J (+ K L) 0)))
      )
      (INV_MAIN_2 E D G C I B K A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 A E D C B H G F)
        (let ((a!1 (not (= (select F (+ G H)) 32)))
      (a!2 (not (= (select C (+ D E)) 9)))
      (a!3 (not (= (select C (+ D E)) 61)))
      (a!4 (not (= (select C (+ D E)) 32)))
      (a!5 (not (= (select F (+ G H)) 9))))
  (and (= (select F (+ G H)) 61) a!1 a!2 a!3 a!4 a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 A E D C B H G F)
        (let ((a!1 (not (= (select F (+ G H)) 61)))
      (a!2 (not (= (select F (+ G H)) 32)))
      (a!3 (not (= (select C (+ D E)) 9)))
      (a!4 (not (= (select C (+ D E)) 32)))
      (a!5 (not (= (select F (+ G H)) 9))))
  (and a!1 a!2 a!3 (= (select C (+ D E)) 61) a!4 a!5))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G (Array Int Int)) (H (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_2 A D C G B F E H)
        (let ((a!1 (not (= (select G (+ C D)) 9)))
      (a!2 (not (= (select G (+ C D)) 61)))
      (a!3 (not (= (select G (+ C D)) 32)))
      (a!4 (not (= (select H (+ E F)) 9)))
      (a!5 (not (= (select H (+ E F)) 61)))
      (a!6 (not (= (select H (+ E F)) 32))))
  (and a!1 a!2 a!3 a!4 a!5 a!6 (not (= G H))))
      )
      END_QUERY
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
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_3 B D C A F H G E)
        (let ((a!1 (not (= (select A (+ 1 C D)) 9)))
      (a!2 (not (= (select A (+ 1 C D)) 32)))
      (a!3 (not (= (select E (+ 1 G H)) 9)))
      (a!4 (not (= (select E (+ 1 G H)) 32)))
      (a!5 (not (= (store A B (+ 1 C D)) (store E F (+ 1 G H))))))
  (and a!1 a!2 a!3 a!4 a!5))
      )
      END_QUERY
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
