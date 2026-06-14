(set-logic HORN)


(declare-fun |END_QUERY| ( ) Bool)
(declare-fun |INV_MAIN_42| ( Int Int Int Int (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I (Array Int Int)) (v_9 Int) (v_10 Int) ) 
    (=>
      (and
        (and (= D H)
     (= C G)
     (= B F)
     (not (<= B (+ C D)))
     (= (select E A) (select I A))
     (= 0 v_9)
     (= v_10 F))
      )
      (INV_MAIN_42 B C v_9 D E F v_10 G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 A B D E I G F C H J)
        (let ((a!1 (<= H (div (+ F (* (- 1) G)) 4))))
  (and a!1 (<= E D) (not (= I J))))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L Int) (M Int) (N (Array Int Int)) (O Int) ) 
    (=>
      (and
        (INV_MAIN_42 I G J F H K M O L N)
        (let ((a!1 (store N M (+ (select N M) (select N O))))
      (a!4 (<= L (div (+ M (* (- 1) K)) 4)))
      (a!5 (store H (+ I (* 4 J)) (select H (+ G (* 4 J))))))
(let ((a!2 (store a!1 O (+ (select N M) (select N O) (* (- 1) (select a!1 O)))))
      (a!6 (store a!5 (+ G (* 4 J)) (select H (+ I (* 4 J))))))
(let ((a!3 (store a!2
                  M
                  (+ (select a!2 M)
                     (* (- 1) (select N M))
                     (* (- 1) (select N O))
                     (select a!1 O)))))
  (and (= A a!3)
       (= E (+ 1 J))
       (= B (+ 4 O))
       (= C (+ 4 M))
       (not (<= F J))
       (not a!4)
       (= D a!6)))))
      )
      (INV_MAIN_42 I G E F D K C B L A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_42 F D G C E H I J K L)
        (let ((a!1 (<= K (div (+ I (* (- 1) H)) 4)))
      (a!2 (store E (+ F (* 4 G)) (select E (+ D (* 4 G))))))
(let ((a!3 (store a!2 (+ D (* 4 G)) (select E (+ F (* 4 G))))))
  (and (= B (+ 1 G)) (not (<= C G)) a!1 (= A a!3))))
      )
      (INV_MAIN_42 F D B C A H I J K L)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Int) (K Int) (L (Array Int Int)) (M Int) ) 
    (=>
      (and
        (INV_MAIN_42 D E F G H I K M J L)
        (let ((a!1 (<= J (div (+ K (* (- 1) I)) 4)))
      (a!2 (store L K (+ (select L K) (select L M)))))
(let ((a!3 (store a!2 M (+ (select L K) (select L M) (* (- 1) (select a!2 M))))))
(let ((a!4 (store a!3
                  K
                  (+ (select a!3 K)
                     (* (- 1) (select L K))
                     (* (- 1) (select L M))
                     (select a!2 M)))))
  (and (= C (+ 4 K)) (= B (+ 4 M)) (not a!1) (<= G F) (= A a!4)))))
      )
      (INV_MAIN_42 D E F G H I C B J A)
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
