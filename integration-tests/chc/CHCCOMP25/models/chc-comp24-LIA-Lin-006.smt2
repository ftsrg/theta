(set-logic HORN)


(declare-fun |main@entry| ( ) Bool)
(declare-fun |main@tailrecurse.i| ( Int Int Int Int ) Bool)
(declare-fun |main@sum.exit.split| ( ) Bool)

(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      main@entry
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        main@entry
        (and (or (not E) (not B) (not A))
     (or (not E) (not D) (= C G))
     (or (not E) (not D) (= F H))
     (or (not E) (not D) (= I F))
     (or (not E) (not D) (= J C))
     (or (not D) (and E D))
     (or (not E) (and E A))
     (= D true)
     (= B (= H 0)))
      )
      (main@tailrecurse.i G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (main@tailrecurse.i J K A B)
        (and (= D (+ 1 B))
     (= E (+ (- 1) A))
     (or (not H) (not G) (= F D))
     (or (not H) (not G) (= I E))
     (or (not H) (not G) (= L I))
     (or (not H) (not G) (= M F))
     (or (not H) (not G) (not C))
     (or (not G) (and H G))
     (= G true)
     (= C (= E 0)))
      )
      (main@tailrecurse.i J K L M)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Bool) ) 
    (=>
      (and
        main@entry
        (and (or (not B) (= C D) (not I))
     (or (not B) (= F C) (not I))
     (or (not B) A (not I))
     (or (not I) (= H (= F G)))
     (or (not I) (= G (+ D E)))
     (or (not I) (and B I))
     (or (not I) H)
     (or (not J) (and J I))
     (= J true)
     (= A (= E 0)))
      )
      main@sum.exit.split
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Bool) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Bool) (P Bool) (Q Bool) ) 
    (=>
      (and
        (main@tailrecurse.i K L A B)
        (and (= C (+ (- 1) A))
     (= E (+ 1 B))
     (or (not I) (not F) (= G E))
     (or (not I) (not F) (= H G))
     (or (not I) (not F) D)
     (or (not I) (= J H) (not P))
     (or (not I) (= M J) (not P))
     (or (not P) (= O (= M N)))
     (or (not P) (= N (+ K L)))
     (or (not P) (and I P))
     (or (not P) O)
     (or (not Q) (and Q P))
     (or (not I) (and I F))
     (= Q true)
     (= D (= C 0)))
      )
      main@sum.exit.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@sum.exit.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
