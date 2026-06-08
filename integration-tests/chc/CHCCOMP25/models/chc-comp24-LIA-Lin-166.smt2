(set-logic HORN)


(declare-fun |INV_MAIN_4| ( Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_3| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_1| ( Int Int Int Int Int Int ) Bool)
(declare-fun |INV_MAIN_2| ( Int Int Int Int Int Int ) Bool)
(declare-fun |END_QUERY| ( ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) ) 
    (=>
      (and
        (and (= A B) (= 1 v_2) (= 1 v_3) (= 1 v_4) (= 1 v_5))
      )
      (INV_MAIN_1 v_2 A v_3 v_4 B v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_1 E F G H I J)
        (and (= C G) (= B (+ 1 H)) (= A J) (<= E F) (<= H I) (= D (+ 1 E)))
      )
      (INV_MAIN_1 D F C B I A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H)
        (and (= A E) (<= C D) (not (<= F G)) (= B (+ 1 C)))
      )
      (INV_MAIN_1 B D A F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_1 C D E F G H)
        (and (= A H) (not (<= C D)) (<= F G) (= B (+ 1 F)))
      )
      (INV_MAIN_1 C D E B G A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (INV_MAIN_1 A C D B E F)
        (and (not (<= B E)) (not (<= A C)) (= 0 v_6) (= 1 v_7))
      )
      (INV_MAIN_2 v_6 C D v_7 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_2 G E F J H I)
        (and (= C (+ F G)) (= B (+ 1 J)) (= A (+ I J)) (<= G E) (<= J H) (= D (+ 1 G)))
      )
      (INV_MAIN_2 D E C B H A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 E C D F G H)
        (and (= A (+ D E)) (<= E C) (not (<= F G)) (= B (+ 1 E)))
      )
      (INV_MAIN_2 B C A F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_2 C D E H F G)
        (and (= A (+ G H)) (not (<= C D)) (<= H F) (= B (+ 1 H)))
      )
      (INV_MAIN_2 C D E B F A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (INV_MAIN_2 A C D B E F)
        (and (not (<= B E)) (not (<= A C)) (= 1 v_6) (= 1 v_7))
      )
      (INV_MAIN_3 v_6 C D v_7 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_3 E F G H I J)
        (and (= C (* 2 G)) (= B (+ 1 H)) (= A (* 2 J)) (<= E F) (<= H I) (= D (+ 1 E)))
      )
      (INV_MAIN_3 D F C B I A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_3 C D E F G H)
        (and (= A (* 2 E)) (<= C D) (not (<= F G)) (= B (+ 1 C)))
      )
      (INV_MAIN_3 B D A F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_3 C D E F G H)
        (and (= A (* 2 H)) (not (<= C D)) (<= F G) (= B (+ 1 F)))
      )
      (INV_MAIN_3 C D E B G A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_3 A C D B E F)
        (and (not (<= B E)) (not (<= A C)))
      )
      (INV_MAIN_4 C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (INV_MAIN_4 A C B D)
        (and (not (>= A 0)) (<= B 0) (not (= C D)))
      )
      END_QUERY
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_4 F E H G)
        (and (= D (+ (- 1) F))
     (= B (+ (- 1) H))
     (= A (+ G H))
     (>= F 0)
     (not (<= H 0))
     (= C (+ E F)))
      )
      (INV_MAIN_4 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_4 D C E F)
        (and (= B (+ (- 1) D)) (>= D 0) (<= E 0) (= A (+ C D)))
      )
      (INV_MAIN_4 B A E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_4 C D F E)
        (and (= B (+ (- 1) F)) (not (>= C 0)) (not (<= F 0)) (= A (+ E F)))
      )
      (INV_MAIN_4 C D B A)
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
